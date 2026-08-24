/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicSingleTransientVariation
import MathUE.Probability.MarkovStateEliminationChronology

/-!
# Duration-labelled renewal law for one eliminated Markov state

An excursion from a pivot consists of geometrically many self-loops followed by an exit to a
different state.  The law below retains both the exit state and the actual positive duration.
This is the chronology-preserving replacement for an ordinary same-clock Schur edge.
-/

namespace Math.Probability

noncomputable section

open Filter

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- States other than the pivot, used as literal exit labels. -/
abbrev PivotExitState (pivot : State) := {state : State // state ≠ pivot}

/-- One-step probability of leaving the pivot. -/
def pivotExitProbability (kernel : State → PMF State) (pivot : State) : ℝ :=
  1 - (kernel pivot pivot).toReal

omit [Fintype State] [DecidableEq State] in
theorem pivotExitProbability_pos
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < 1 - (kernel pivot pivot).toReal) :
    0 < pivotExitProbability kernel pivot := exit_pos

omit [Fintype State] [DecidableEq State] in
theorem pivotExitProbability_le_one (kernel : State → PMF State) (pivot : State) :
    pivotExitProbability kernel pivot ≤ 1 := by
  exact sub_le_self 1 ENNReal.toReal_nonneg

theorem sum_pivot_exit_mass
    (kernel : State → PMF State) (pivot : State) :
    ∑ exit : PivotExitState pivot, (kernel pivot exit.1).toReal =
      pivotExitProbability kernel pivot := by
  rw [← Finset.sum_subtype (Finset.univ.erase pivot) (by simp) fun state ↦
    (kernel pivot state).toReal]
  have htotal := pmf_toReal_sum_one (kernel pivot)
  have hdecomp := Finset.sum_erase_add Finset.univ
    (fun state ↦ (kernel pivot state).toReal) (Finset.mem_univ pivot)
  rw [htotal] at hdecomp
  simp only [pivotExitProbability]
  linarith

/-- Conditional law of the first non-pivot state reached when the pivot exits. -/
def pivotExitLaw
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot) : PMF (PivotExitState pivot) :=
  PMF.ofFintype
    (fun exit ↦ ENNReal.ofReal
      ((kernel pivot exit.1).toReal / pivotExitProbability kernel pivot))
    (by
      rw [← ENNReal.ofReal_one,
        ← show (∑ exit : PivotExitState pivot,
            (kernel pivot exit.1).toReal / pivotExitProbability kernel pivot) = 1 by
          rw [← Finset.sum_div, sum_pivot_exit_mass]
          exact div_self exit_pos.ne']
      exact (ENNReal.ofReal_sum_of_nonneg (fun exit _ ↦
        div_nonneg ENNReal.toReal_nonneg exit_pos.le)).symm)

@[simp]
theorem pivotExitLaw_toReal
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (exit : PivotExitState pivot) :
    (pivotExitLaw kernel pivot exit_pos exit).toReal =
      (kernel pivot exit.1).toReal / pivotExitProbability kernel pivot := by
  rw [pivotExitLaw, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact div_nonneg ENNReal.toReal_nonneg exit_pos.le

/-- Geometric count of failures before the first success, as a PMF. -/
def renewalGeometricPMF
    (success : ℝ) (success_pos : 0 < success) (success_le_one : success ≤ 1) : PMF ℕ :=
  ⟨fun failures ↦ ENNReal.ofReal ((1 - success) ^ failures * success), by
    apply ENNReal.hasSum_coe.mpr
    have hgeom := hasSum_geometric_of_lt_one
      (sub_nonneg.mpr success_le_one) (sub_lt_self 1 success_pos)
    have hsum : HasSum (fun failures : ℕ ↦ (1 - success) ^ failures * success) 1 := by
      have h := hgeom.mul_right success
      simpa [inv_mul_eq_div, div_self success_pos.ne'] using h
    simpa using hsum.toNNReal (fun failures ↦
      mul_nonneg (pow_nonneg (sub_nonneg.mpr success_le_one) failures) success_pos.le)⟩

@[simp]
theorem renewalGeometricPMF_toReal
    (success : ℝ) (success_pos : 0 < success) (success_le_one : success ≤ 1)
    (failures : ℕ) :
    (renewalGeometricPMF success success_pos success_le_one failures).toReal =
      (1 - success) ^ failures * success := by
  change (ENNReal.ofReal ((1 - success) ^ failures * success)).toReal = _
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (pow_nonneg (sub_nonneg.mpr success_le_one) failures) success_pos.le

/-- Joint law of the exit state and the positive pivot-to-exit duration. -/
def pivotExcursionRenewalLaw
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot) :
    PMF (PivotExitState pivot × ℕ) :=
  (renewalGeometricPMF (pivotExitProbability kernel pivot) exit_pos
      (pivotExitProbability_le_one kernel pivot)).bind fun failures ↦
    (pivotExitLaw kernel pivot exit_pos).map fun exit ↦ (exit, failures + 1)

theorem pivotExcursionRenewalLaw_total_mass
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot) :
    ∑' outcome, pivotExcursionRenewalLaw kernel pivot exit_pos outcome = 1 :=
  PMF.tsum_coe _

theorem expect_pivotExitLaw
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (payoff : PivotExitState pivot → ℝ) :
    expect (pivotExitLaw kernel pivot exit_pos) payoff =
      (∑ exit : PivotExitState pivot,
        (kernel pivot exit.1).toReal * payoff exit) /
          pivotExitProbability kernel pivot := by
  rw [expect_eq_sum]
  simp_rw [pivotExitLaw_toReal, div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem expect_renewalGeometricPMF
    (success : ℝ) (success_pos : 0 < success) (success_le_one : success ≤ 1)
    (payoff : ℕ → ℝ) :
    expect (renewalGeometricPMF success success_pos success_le_one) payoff =
      ∑' failures : ℕ, (1 - success) ^ failures * success * payoff failures := by
  unfold expect
  apply tsum_congr
  intro failures
  rw [renewalGeometricPMF_toReal]

/-- The duration-labelled exit series sums to the current pivot value. -/
theorem hasSum_pivotExcursionExitValue
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (exit_pos : 0 < pivotExitProbability kernel pivot) (time : ℕ) :
    HasSum (fun failures : ℕ ↦
      (kernel pivot pivot).toReal ^ failures *
        pivotExitValue (fun source target ↦ (kernel source target).toReal)
          value pivot (time + failures + 1))
      (value pivot time) := by
  let matrix : State → State → ℝ :=
    fun source target ↦ (kernel source target).toReal
  let q := matrix pivot pivot
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq_lt : q < 1 := by
    simpa [q, matrix, pivotExitProbability] using exit_pos
  have hmatrix0 (source target : State) : 0 ≤ matrix source target :=
    ENNReal.toReal_nonneg
  have hmatrixSum (source : State) : ∑ target, matrix source target = 1 :=
    pmf_toReal_sum_one (kernel source)
  have hmatrixHarmonic (state : State) (current : ℕ) :
      value state current =
        ∑ target, matrix state target * value target (current + 1) := by
    rw [harmonic.2 state current, expect_eq_sum]
  have hexit0 (current : ℕ) :
      0 ≤ pivotExitValue matrix value pivot current := by
    apply Finset.sum_nonneg
    intro target _
    exact mul_nonneg (hmatrix0 pivot target) (harmonic.1 target current).1
  have hterm0 (failures : ℕ) :
      0 ≤ q ^ failures *
        pivotExitValue matrix value pivot (time + failures + 1) :=
    mul_nonneg (pow_nonneg hq0 failures) (hexit0 _)
  apply (hasSum_iff_tendsto_nat_of_nonneg hterm0 _).2
  have hrem : Tendsto
      (fun rounds : ℕ ↦ q ^ rounds * value pivot (time + rounds))
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro rounds
      exact mul_nonneg (pow_nonneg hq0 rounds) (harmonic.1 pivot _).1
    · intro rounds
      exact mul_le_of_le_one_right (pow_nonneg hq0 rounds) (harmonic.1 pivot _).2
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq_lt
  have hpartial : Tendsto
      (fun rounds : ℕ ↦ value pivot time -
        q ^ rounds * value pivot (time + rounds))
      atTop (nhds (value pivot time)) := by
    simpa using hrem.const_sub (value pivot time)
  convert hpartial using 1
  funext rounds
  have hunroll := backwardHarmonic_pivot_unroll
    matrix value pivot hmatrixHarmonic time rounds
  rw [hunroll]
  ring

/-- Backward harmonicity transported through the renewal law with the actual elapsed time. -/
theorem expect_pivotExcursionRenewalLaw_value
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (exit_pos : 0 < pivotExitProbability kernel pivot) (time : ℕ) :
    expect (pivotExcursionRenewalLaw kernel pivot exit_pos) (fun outcome ↦
      value outcome.1.1 (time + outcome.2)) = value pivot time := by
  let success := pivotExitProbability kernel pivot
  let durationLaw := renewalGeometricPMF success exit_pos
    (pivotExitProbability_le_one kernel pivot)
  let exitLaw := pivotExitLaw kernel pivot exit_pos
  have hbound (outcome : PivotExitState pivot × ℕ) :
      |value outcome.1.1 (time + outcome.2)| ≤ 1 := by
    rcases harmonic.1 outcome.1.1 (time + outcome.2) with ⟨hvalue0, hvalue1⟩
    rw [abs_le]
    constructor <;> linarith
  rw [show pivotExcursionRenewalLaw kernel pivot exit_pos =
      durationLaw.bind (fun failures ↦
        exitLaw.map fun exit ↦ (exit, failures + 1)) by rfl]
  rw [expect_bind_of_bounded durationLaw
    (fun failures ↦ exitLaw.map fun exit ↦ (exit, failures + 1))
    (fun outcome ↦ value outcome.1.1 (time + outcome.2)) hbound]
  simp_rw [expect_map]
  rw [show durationLaw = renewalGeometricPMF success exit_pos
      (pivotExitProbability_le_one kernel pivot) by rfl,
    expect_renewalGeometricPMF]
  simp_rw [show exitLaw = pivotExitLaw kernel pivot exit_pos by rfl,
    expect_pivotExitLaw]
  have hseries := (hasSum_pivotExcursionExitValue
    kernel pivot value harmonic exit_pos time).tsum_eq
  rw [← hseries]
  apply tsum_congr
  intro failures
  have hexitSum :
      (∑ exit : PivotExitState pivot,
        (kernel pivot exit.1).toReal * value exit.1 (time + (failures + 1))) =
        pivotExitValue (fun source target ↦ (kernel source target).toReal)
          value pivot (time + failures + 1) := by
    rw [← Finset.sum_subtype (Finset.univ.erase pivot) (by simp) fun state ↦
      (kernel pivot state).toReal * value state (time + (failures + 1))]
    simp only [pivotExitValue]
    congr 1
  rw [hexitSum]
  change (1 - success) ^ failures * success *
      (_ / success) = (kernel pivot pivot).toReal ^ failures * _
  have hsuccess : success = 1 - (kernel pivot pivot).toReal := rfl
  have hexitne : 1 - (kernel pivot pivot).toReal ≠ 0 := by
    simpa [success, pivotExitProbability] using exit_pos.ne'
  rw [hsuccess, show 1 - (1 - (kernel pivot pivot).toReal) =
    (kernel pivot pivot).toReal by ring]
  field_simp [hexitne]

/-- Duration-labelled reduced row after eliminating the pivot.  A direct transition has
duration one; a transition entering the pivot adds one entry step to the pivot excursion. -/
def pivotEliminatedRenewalKernel
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (source : PivotExitState pivot) : PMF (PivotExitState pivot × ℕ) :=
  (kernel source.1).bind fun successor ↦
    if successor_eq : successor = pivot then
      (pivotExcursionRenewalLaw kernel pivot exit_pos).map fun outcome ↦
        (outcome.1, outcome.2 + 1)
    else
      PMF.pure (⟨successor, successor_eq⟩, 1)

theorem pivotEliminatedRenewalKernel_total_mass
    (kernel : State → PMF State) (pivot : State)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (source : PivotExitState pivot) :
    ∑' outcome, pivotEliminatedRenewalKernel kernel pivot exit_pos source outcome = 1 :=
  PMF.tsum_coe _

/-- The restricted backward-harmonic orbit is harmonic for the duration-labelled reduced
kernel, with no phase loss: each outcome is evaluated at its actual elapsed duration. -/
theorem expect_pivotEliminatedRenewalKernel_value
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (source : PivotExitState pivot) (time : ℕ) :
    expect (pivotEliminatedRenewalKernel kernel pivot exit_pos source) (fun outcome ↦
      value outcome.1.1 (time + outcome.2)) = value source.1 time := by
  let payoff : PivotExitState pivot × ℕ → ℝ := fun outcome ↦
    value outcome.1.1 (time + outcome.2)
  have hbound (outcome : PivotExitState pivot × ℕ) : |payoff outcome| ≤ 1 := by
    rcases harmonic.1 outcome.1.1 (time + outcome.2) with ⟨hvalue0, hvalue1⟩
    dsimp [payoff]
    rw [abs_le]
    constructor <;> linarith
  rw [show pivotEliminatedRenewalKernel kernel pivot exit_pos source =
      (kernel source.1).bind fun successor ↦
        if successor_eq : successor = pivot then
          (pivotExcursionRenewalLaw kernel pivot exit_pos).map fun outcome ↦
            (outcome.1, outcome.2 + 1)
        else PMF.pure (⟨successor, successor_eq⟩, 1) by rfl]
  rw [expect_bind_of_bounded (kernel source.1)
    (fun successor ↦
      if successor_eq : successor = pivot then
        (pivotExcursionRenewalLaw kernel pivot exit_pos).map fun outcome ↦
          (outcome.1, outcome.2 + 1)
      else PMF.pure (⟨successor, successor_eq⟩, 1)) payoff hbound]
  have hinner (successor : State) :
      expect (if successor_eq : successor = pivot then
          (pivotExcursionRenewalLaw kernel pivot exit_pos).map fun outcome ↦
            (outcome.1, outcome.2 + 1)
        else PMF.pure (⟨successor, successor_eq⟩, 1)) payoff =
        value successor (time + 1) := by
    by_cases successor_eq : successor = pivot
    · subst successor
      rw [dif_pos rfl, expect_map]
      have hpivot := expect_pivotExcursionRenewalLaw_value
        kernel pivot value harmonic exit_pos (time + 1)
      change expect (pivotExcursionRenewalLaw kernel pivot exit_pos)
        (fun outcome : PivotExitState pivot × ℕ ↦
          value outcome.1.1 (time + (outcome.2 + 1))) = value pivot (time + 1)
      rw [show (fun outcome : PivotExitState pivot × ℕ ↦
          value outcome.1.1 (time + (outcome.2 + 1))) =
          (fun outcome ↦ value outcome.1.1 (time + 1 + outcome.2)) by
        funext outcome
        apply congrArg (value outcome.1.1)
        omega]
      exact hpivot
    · rw [dif_neg successor_eq, expect_pure]
  simp_rw [hinner]
  exact (harmonic.2 source.1 time).symm

/-- Bernoulli variation potential of a unit-interval scalar. -/
def bernoulliVariationPotential (current : ℝ) : ℝ :=
  2 * Real.sqrt (current * (1 - current))

theorem bernoulliVariationPotential_nonneg (current : ℝ) :
    0 ≤ bernoulliVariationPotential current := by
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- Conditional one-step absolute variation at the pivot. -/
def pivotLocalVariation
    (kernel : State → PMF State) (value : State → ℕ → ℝ)
    (pivot : State) (time : ℕ) : ℝ :=
  expect (kernel pivot) (fun successor ↦
    |value successor (time + 1) - value pivot time|)

omit [Fintype State] [DecidableEq State] in
theorem pivotLocalVariation_nonneg
    (kernel : State → PMF State) (value : State → ℕ → ℝ)
    (pivot : State) (time : ℕ) :
    0 ≤ pivotLocalVariation kernel value pivot time := by
  apply expect_nonneg
  exact fun _ ↦ abs_nonneg _

/-- One-step peeling: current pivot potential pays local variation and the self-loop's next
potential. -/
theorem pivotLocalVariation_add_selfPotential_le
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value) (time : ℕ) :
    pivotLocalVariation kernel value pivot time +
        (kernel pivot pivot).toReal *
          bernoulliVariationPotential (value pivot (time + 1)) ≤
      bernoulliVariationPotential (value pivot time) := by
  have honeAtom := expect_abs_sub_expect_add_atom_bernoulliPotential_le
    (kernel pivot) pivot (fun successor ↦ value successor (time + 1))
    (fun successor ↦ harmonic.1 successor (time + 1))
  rw [← harmonic.2 pivot time] at honeAtom
  simp only [pivotLocalVariation, bernoulliVariationPotential] at honeAtom ⊢
  nlinarith

theorem sum_pivotLocalVariation_add_remainder_le
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (time rounds : ℕ) :
    (∑ step ∈ Finset.range rounds,
        (kernel pivot pivot).toReal ^ step *
          pivotLocalVariation kernel value pivot (time + step)) +
      (kernel pivot pivot).toReal ^ rounds *
        bernoulliVariationPotential (value pivot (time + rounds)) ≤
      bernoulliVariationPotential (value pivot time) := by
  let q := (kernel pivot pivot).toReal
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hlocal := pivotLocalVariation_add_selfPotential_le
        kernel pivot value harmonic (time + rounds)
      have hscaled := mul_le_mul_of_nonneg_left hlocal (pow_nonneg hq0 rounds)
      change (∑ step ∈ Finset.range rounds,
          q ^ step * pivotLocalVariation kernel value pivot (time + step)) +
          q ^ rounds * pivotLocalVariation kernel value pivot (time + rounds) +
          (q ^ rounds * q) *
            bernoulliVariationPotential (value pivot (time + (rounds + 1))) ≤
        bernoulliVariationPotential (value pivot time)
      have htime : time + (rounds + 1) = time + rounds + 1 := by omega
      rw [htime]
      nlinarith

/-- Expected variation accumulated while the process remains at the pivot and on its eventual
exit is at most one Bernoulli potential.  The left side is the exact geometric local-variation
series; its identification with the explicit renewal-path payoff is the remaining Fubini
adapter. -/
theorem tsum_pivotLocalVariation_le_bernoulliPotential
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value) (time : ℕ) :
    (∑' step : ℕ, (kernel pivot pivot).toReal ^ step *
        pivotLocalVariation kernel value pivot (time + step)) ≤
      bernoulliVariationPotential (value pivot time) := by
  apply Real.tsum_le_of_sum_range_le
  · intro step
    exact mul_nonneg (pow_nonneg ENNReal.toReal_nonneg step)
      (pivotLocalVariation_nonneg kernel value pivot (time + step))
  · intro rounds
    have h := sum_pivotLocalVariation_add_remainder_le
      kernel pivot value harmonic time rounds
    have hremainder :
        0 ≤ (kernel pivot pivot).toReal ^ rounds *
          bernoulliVariationPotential (value pivot (time + rounds)) :=
      mul_nonneg (pow_nonneg ENNReal.toReal_nonneg rounds)
        (bernoulliVariationPotential_nonneg _)
    linarith

/-- Jensen's absolute-deviation inequality for a bounded function on an arbitrary countable
PMF.  Unlike the finite-state convenience lemma, this applies to renewal laws with infinite
duration support. -/
theorem abs_expect_sub_const_le_expect_abs_sub_const_of_bounded
    {Outcome : Type*} (law : PMF Outcome) (payoff : Outcome → ℝ)
    (center bound : ℝ) (bounded : ∀ outcome, |payoff outcome| ≤ bound) :
    |expect law payoff - center| ≤
      expect law (fun outcome ↦ |payoff outcome - center|) := by
  have hpayoff := expect_summable_of_bounded law payoff bounded
  have hcenter := expect_summable_of_bounded law (fun _ ↦ -center)
    (C := |center|) (fun _ ↦ by simp)
  have hsub : expect law (fun outcome ↦ payoff outcome - center) =
      expect law payoff - center := by
    have hadd := expect_add_of_summable law payoff (fun _ ↦ -center) hpayoff hcenter
    simpa [sub_eq_add_neg] using hadd
  have hcenteredBound (outcome : Outcome) :
      |payoff outcome - center| ≤ bound + |center| := by
    calc
      |payoff outcome - center| ≤ |payoff outcome| + |center| := by
        simpa using abs_sub (payoff outcome) center
      _ ≤ bound + |center| := by
        simpa only [add_comm] using add_le_add_right (bounded outcome) |center|
  have hcentered := expect_summable_of_bounded law
    (fun outcome ↦ payoff outcome - center) hcenteredBound
  have habs := expect_summable_of_bounded law
    (fun outcome ↦ |payoff outcome - center|) (fun outcome ↦ by
      simpa only [abs_abs] using hcenteredBound outcome)
  rcases le_total 0 (expect law payoff - center) with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg, ← hsub]
    exact hcentered.tsum_le_tsum (fun outcome ↦
      mul_le_mul_of_nonneg_left (le_abs_self _) ENNReal.toReal_nonneg) habs
  · rw [abs_of_nonpos hnonpos, ← hsub, ← expect_neg]
    have hneg : Summable (fun outcome ↦
        (law outcome).toReal * (-(payoff outcome - center))) := by
      simpa only [mul_neg] using hcentered.neg
    exact hneg.tsum_le_tsum (fun outcome ↦
      mul_le_mul_of_nonneg_left (neg_le_abs _) ENNReal.toReal_nonneg) habs

/-- Exact duration-aware excursion comparison.  The entry edge followed by the geometrically
weighted pivot local-variation account is bounded by the renewal endpoint variation plus one
Bernoulli pivot potential.  Thus collapsing the excursion does not lose chronology or require
an independent per-visit budget. -/
theorem pivotExcursionVariation_le_reduced_add_potential
    (kernel : State → PMF State) (pivot : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (exit_pos : 0 < pivotExitProbability kernel pivot)
    (entryValue : ℝ) (time : ℕ) :
    |value pivot time - entryValue| +
        ∑' step : ℕ, (kernel pivot pivot).toReal ^ step *
          pivotLocalVariation kernel value pivot (time + step) ≤
      expect (pivotExcursionRenewalLaw kernel pivot exit_pos) (fun outcome ↦
        |value outcome.1.1 (time + outcome.2) - entryValue|) +
      bernoulliVariationPotential (value pivot time) := by
  have hpayoffBound (outcome : PivotExitState pivot × ℕ) :
      |value outcome.1.1 (time + outcome.2)| ≤ 1 := by
    rcases harmonic.1 outcome.1.1 (time + outcome.2) with ⟨hvalue0, hvalue1⟩
    rw [abs_le]
    constructor <;> linarith
  have hjensen := abs_expect_sub_const_le_expect_abs_sub_const_of_bounded
    (pivotExcursionRenewalLaw kernel pivot exit_pos)
    (fun outcome ↦ value outcome.1.1 (time + outcome.2)) entryValue 1 hpayoffBound
  rw [expect_pivotExcursionRenewalLaw_value
    kernel pivot value harmonic exit_pos time] at hjensen
  have hvariation := tsum_pivotLocalVariation_le_bernoulliPotential
    kernel pivot value harmonic time
  linarith

/-- Predecessor-facing form: an entry step at displayed time `time`, followed by the whole
pivot excursion, is bounded by the duration-aware collapsed endpoint variation plus one pivot
potential at the entry time. -/
theorem pivotEntryExcursionVariation_le_reduced_add_potential
    (kernel : State → PMF State) (pivot source : State) (value : State → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (exit_pos : 0 < pivotExitProbability kernel pivot) (time : ℕ) :
    |value pivot (time + 1) - value source time| +
        ∑' step : ℕ, (kernel pivot pivot).toReal ^ step *
          pivotLocalVariation kernel value pivot (time + 1 + step) ≤
      expect (pivotExcursionRenewalLaw kernel pivot exit_pos) (fun outcome ↦
        |value outcome.1.1 (time + 1 + outcome.2) - value source time|) +
      bernoulliVariationPotential (value pivot (time + 1)) := by
  exact pivotExcursionVariation_le_reduced_add_potential
    kernel pivot value harmonic exit_pos (value source time) (time + 1)

end

end Math.Probability
