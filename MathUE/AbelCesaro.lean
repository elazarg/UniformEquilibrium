import Mathlib
import MathUE.BanachLimit

/-!
# Abel bounds for survival-weighted Cesàro averages

An antitone survival weight can splice a payoff sequence into a fallback
value.  If the unweighted Cesàro averages converge to `v` and the fallback is
at most `v`, this splice cannot have Banach value above `v`.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace MathUE

/-- Summation by parts for a finite weighted sum. -/
theorem sum_mul_eq_sum_weightStep_mul_partialSum (weight summand : ℕ → ℝ)
    (horizon : ℕ) :
    ∑ stage ∈ Finset.range horizon, weight stage * summand stage =
      (∑ stage ∈ Finset.range horizon,
          (weight stage - weight (stage + 1)) *
            ∑ earlier ∈ Finset.range (stage + 1), summand earlier) +
        weight horizon * ∑ earlier ∈ Finset.range horizon, summand earlier := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ (f := fun stage ↦ weight stage * summand stage),
        Finset.sum_range_succ (f := fun stage ↦
          (weight stage - weight (stage + 1)) *
            ∑ earlier ∈ Finset.range (stage + 1), summand earlier),
        ih, Finset.sum_range_succ (f := summand) (n := horizon)]
      ring

/-- Abel's inequality for nonnegative antitone weights. -/
theorem sum_mul_le_initialWeight_mul_of_partialSum_le
    {weight summand : ℕ → ℝ} {ε : ℝ} (horizon : ℕ)
    (hanti : ∀ stage, weight (stage + 1) ≤ weight stage)
    (hlast : 0 ≤ weight horizon)
    (hpartial : ∀ index, index ≤ horizon →
      ∑ earlier ∈ Finset.range index, summand earlier ≤ ε) :
    ∑ stage ∈ Finset.range horizon, weight stage * summand stage ≤
      weight 0 * ε := by
  have hstepBound : ∀ stage ∈ Finset.range horizon,
      (weight stage - weight (stage + 1)) *
          ∑ earlier ∈ Finset.range (stage + 1), summand earlier ≤
        (weight stage - weight (stage + 1)) * ε := by
    intro stage hstage
    exact mul_le_mul_of_nonneg_left
      (hpartial (stage + 1) (Finset.mem_range.mp hstage))
      (sub_nonneg.mpr (hanti stage))
  have hfinal : weight horizon *
        ∑ earlier ∈ Finset.range horizon, summand earlier ≤
      weight horizon * ε :=
    mul_le_mul_of_nonneg_left (hpartial horizon le_rfl) hlast
  have htelescope :
      ∑ stage ∈ Finset.range horizon,
          (weight stage - weight (stage + 1)) * ε =
        (weight 0 - weight horizon) * ε := by
    rw [← Finset.sum_mul, Finset.sum_range_sub' weight horizon]
  rw [sum_mul_eq_sum_weightStep_mul_partialSum weight summand horizon]
  have hsum := Finset.sum_le_sum hstepBound
  rw [htelescope] at hsum
  nlinarith [hsum, hfinal]

/-- The positive-horizon average of the survival splice between `payoff` and
the constant fallback. -/
def survivalBlendAverage (payoff weight : ℕ → ℝ)
    (fallback : ℝ) (step : ℕ) : ℝ :=
  ((step + 1 : ℕ) : ℝ)⁻¹ *
    ∑ time ∈ Finset.range (step + 1),
      (weight time * payoff time + (1 - weight time) * fallback)

/-- Survival splicing into a fallback below the Cesàro limit is eventually
bounded by that limit plus every positive error. -/
theorem eventually_survivalBlendAverage_le_add
    {payoff weight : ℕ → ℝ} {fallback limit bound : ℝ}
    (hbound : ∀ time, |payoff time| ≤ bound)
    (haverage : Tendsto
      (fun step ↦ ((step + 1 : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range (step + 1), payoff time)
      atTop (nhds limit))
    (hfallback : fallback ≤ limit)
    (hweight0 : ∀ time, 0 ≤ weight time)
    (hweight1 : ∀ time, weight time ≤ 1)
    (hanti : ∀ time, weight (time + 1) ≤ weight time)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ step in atTop,
      survivalBlendAverage payoff weight fallback step ≤ limit + ε := by
  let η := ε / 3
  have hη : 0 < η := by dsimp only [η]; linarith
  have havgEventually : ∀ᶠ step in atTop,
      ((step + 1 : ℕ) : ℝ)⁻¹ *
          ∑ time ∈ Finset.range (step + 1), payoff time < limit + η :=
    (tendsto_order.1 haverage).2 _ (lt_add_of_pos_right _ hη)
  obtain ⟨cut, hcut⟩ := eventually_atTop.1 havgEventually
  let earlyBound : ℝ := cut * (bound + |fallback|)
  have hbound0 : 0 ≤ bound := by
    exact (abs_nonneg (payoff 0)).trans (hbound 0)
  have hearly0 : 0 ≤ earlyBound := by
    dsimp only [earlyBound]
    positivity
  have hgap0 : 0 ≤ limit - fallback + η := by linarith
  have hpartial (horizon index : ℕ) (hindex : index ≤ horizon) :
      ∑ time ∈ Finset.range index, (payoff time - fallback) ≤
        earlyBound + horizon * (limit - fallback + η) := by
    by_cases hlate : cut + 1 ≤ index
    · obtain ⟨step, rfl⟩ : ∃ step, index = step + 1 := by
        exact ⟨index - 1, by omega⟩
      have hstep : cut ≤ step := by omega
      have havg := (hcut step hstep).le
      have hpos : 0 < ((step + 1 : ℕ) : ℝ) := by positivity
      have hsum :
          ∑ time ∈ Finset.range (step + 1), payoff time ≤
            (step + 1 : ℝ) * (limit + η) := by
        have := (inv_mul_le_iff₀ hpos).mp havg
        simpa only [Nat.cast_add, Nat.cast_one] using this
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      have hcast : (step + 1 : ℝ) ≤ horizon := by exact_mod_cast hindex
      calc
        ∑ time ∈ Finset.range (step + 1), payoff time -
              (step + 1 : ℝ) * fallback
            ≤ (step + 1 : ℝ) * (limit - fallback + η) := by
              linarith
        _ ≤ horizon * (limit - fallback + η) := by gcongr
        _ ≤ earlyBound + horizon * (limit - fallback + η) := by
          linarith
    · have hindexCut : index ≤ cut := by omega
      calc
        ∑ time ∈ Finset.range index, (payoff time - fallback)
            ≤ ∑ _time ∈ Finset.range index, (bound + |fallback|) := by
              apply Finset.sum_le_sum
              intro time _
              have hpayoff := (abs_le.mp (hbound time)).2
              linarith [neg_le_abs fallback]
        _ = index * (bound + |fallback|) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_add]
        _ ≤ earlyBound := by
          dsimp only [earlyBound]
          gcongr
        _ ≤ earlyBound + horizon * (limit - fallback + η) := by
          nlinarith
  have hratio : Tendsto
      (fun step : ℕ ↦ earlyBound * ((step + 1 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul earlyBound
  have hratioEventually : ∀ᶠ step in atTop,
      earlyBound * ((step + 1 : ℕ) : ℝ)⁻¹ < η :=
    (tendsto_order.1 hratio).2 _ hη
  filter_upwards [hratioEventually] with step hratioStep
  let horizon := step + 1
  have hweighted := sum_mul_le_initialWeight_mul_of_partialSum_le
    (weight := weight) (summand := fun time ↦ payoff time - fallback)
    horizon hanti (hweight0 horizon) (hpartial horizon)
  have htotal0 : 0 ≤ earlyBound +
      (horizon : ℝ) * (limit - fallback + η) := by positivity
  have hweighted' :
      ∑ time ∈ Finset.range horizon,
          weight time * (payoff time - fallback) ≤
        earlyBound + (horizon : ℝ) * (limit - fallback + η) := by
    exact hweighted.trans (by
      have hmul := mul_le_mul_of_nonneg_right (hweight1 0) htotal0
      simpa using hmul)
  have hhorizon : (0 : ℝ) < horizon := by positivity
  unfold survivalBlendAverage
  dsimp only [horizon] at hweighted'
  simp only [Nat.cast_add, Nat.cast_one] at hweighted'
  rw [show (∑ time ∈ Finset.range (step + 1),
        (weight time * payoff time + (1 - weight time) * fallback)) =
      (step + 1 : ℝ) * fallback +
        ∑ time ∈ Finset.range (step + 1),
          weight time * (payoff time - fallback) by
    rw [show (step + 1 : ℝ) * fallback =
        ∑ _time ∈ Finset.range (step + 1), fallback by
      simp [Finset.sum_const, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro time _
    ring]
  calc
    ((step + 1 : ℕ) : ℝ)⁻¹ *
          ((step + 1 : ℝ) * fallback +
            ∑ time ∈ Finset.range (step + 1),
              weight time * (payoff time - fallback))
        ≤ ((step + 1 : ℕ) : ℝ)⁻¹ *
          ((step + 1 : ℝ) * fallback + earlyBound +
            (step + 1 : ℝ) * (limit - fallback + η)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith
    _ = limit + η +
        earlyBound * ((step + 1 : ℕ) : ℝ)⁻¹ := by
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    _ ≤ limit + 2 * η := by linarith
    _ ≤ limit + ε := by
      dsimp only [η]
      linarith

/-- Banach evaluation of the survival splice cannot exceed the Cesàro limit
when the fallback is no larger than that limit. -/
theorem BanachLimit.eval_survivalBlendAverage_le
    (L : BanachLimit) {payoff weight : ℕ → ℝ}
    {fallback limit bound : ℝ}
    (hbound : ∀ time, |payoff time| ≤ bound)
    (haverage : Tendsto
      (fun step ↦ ((step + 1 : ℕ) : ℝ)⁻¹ *
        ∑ time ∈ Finset.range (step + 1), payoff time)
      atTop (nhds limit))
    (hfallback : fallback ≤ limit)
    (hweight0 : ∀ time, 0 ≤ weight time)
    (hweight1 : ∀ time, weight time ≤ 1)
    (hanti : ∀ time, weight (time + 1) ≤ weight time) :
    L.eval (survivalBlendAverage payoff weight fallback) ≤ limit := by
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg (payoff 0)).trans (hbound 0)
  have hboundedBlend : IsBoundedSequence
      (survivalBlendAverage payoff weight fallback) := by
    have hpoint : ∀ step,
        |survivalBlendAverage payoff weight fallback step| ≤
          bound + |fallback| := by
      intro step
      unfold survivalBlendAverage
      have hterm : ∀ time,
          |weight time * payoff time + (1 - weight time) * fallback| ≤
            bound + |fallback| := by
        intro time
        calc
          _ ≤ weight time * |payoff time| +
              (1 - weight time) * |fallback| := by
            calc
              _ ≤ |weight time * payoff time| +
                  |(1 - weight time) * fallback| := abs_add_le _ _
              _ = _ := by
                rw [abs_mul, abs_mul,
                  abs_of_nonneg (hweight0 time),
                  abs_of_nonneg (sub_nonneg.mpr (hweight1 time))]
          _ ≤ weight time * bound +
              (1 - weight time) * |fallback| := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hbound time) (hweight0 time))
              le_rfl
          _ ≤ bound + |fallback| := by
            nlinarith [
              mul_nonneg (sub_nonneg.mpr (hweight1 time)) hbound0,
              mul_nonneg (hweight0 time) (abs_nonneg fallback)]
      calc
        _ = ((step + 1 : ℕ) : ℝ)⁻¹ *
            |∑ time ∈ Finset.range (step + 1),
              (weight time * payoff time +
                (1 - weight time) * fallback)| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ ((step + 1 : ℕ) : ℝ)⁻¹ *
            ∑ _time ∈ Finset.range (step + 1),
              (bound + |fallback|) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun time _ ↦ hterm time)
        _ = bound + |fallback| := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
    exact ⟨bound + |fallback|, hpoint⟩
  exact L.eval_le_of_eventually_le_add hboundedBlend
    (fun ε hε ↦ eventually_survivalBlendAverage_le_add hbound haverage
      hfallback hweight0 hweight1 hanti hε)

end MathUE
