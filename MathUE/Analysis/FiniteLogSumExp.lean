import GameTheory.Math.OnlineLearning
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Finset.Lattice.Fold

/-! # Finite log-sum-exp, its actual weights and entropy

The tester type is arbitrary finite and nonempty; values are arbitrary reals.
No game, reward, calendar, sign or bounded-value premise is present.
-/

noncomputable section

namespace Math.FiniteLogSumExp

open scoped BigOperators
open scoped Topology

variable {J : Type*} [Fintype J] [Nonempty J]

def partition (temperature : ℝ) (values : J → ℝ) : ℝ :=
  ∑ tester, Real.exp (values tester / temperature)

def weight (temperature : ℝ) (values : J → ℝ) (tester : J) : ℝ :=
  Real.exp (values tester / temperature) / partition temperature values

def smoothMax (temperature : ℝ) (values : J → ℝ) : ℝ :=
  temperature * Real.log (partition temperature values)

def maximum (values : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty values

def weightedMean (temperature : ℝ) (values observable : J → ℝ) : ℝ :=
  ∑ tester, weight temperature values tester * observable tester

def entropy (temperature : ℝ) (values : J → ℝ) : ℝ :=
  ∑ tester, Real.negMulLog (weight temperature values tester)

def inactivity (temperature : ℝ) (values : J → ℝ) : ℝ :=
  ∑ tester, weight temperature values tester * (maximum values - values tester)

theorem partition_pos (temperature : ℝ) (values : J → ℝ) :
    0 < partition temperature values := by
  classical
  exact Finset.sum_pos (fun tester _ => Real.exp_pos _ ) Finset.univ_nonempty

omit [Nonempty J] in
theorem exp_le_partition (temperature : ℝ) (values : J → ℝ) (tester : J) :
    Real.exp (values tester / temperature) ≤ partition temperature values := by
  classical
  exact Finset.single_le_sum (f := fun other : J => Real.exp (values other / temperature))
    (fun other _ => (Real.exp_pos (values other / temperature)).le) (Finset.mem_univ tester)

theorem weight_pos (temperature : ℝ) (values : J → ℝ) (tester : J) :
    0 < weight temperature values tester :=
  div_pos (Real.exp_pos _) (partition_pos temperature values)

theorem weight_le_one (temperature : ℝ) (values : J → ℝ) (tester : J) :
    weight temperature values tester ≤ 1 := by
  apply (div_le_iff₀ (partition_pos temperature values)).mpr
  simpa only [one_mul] using exp_le_partition temperature values tester

omit [Nonempty J] in
/-- This is exactly the canonical arbitrary-score exponential probability. -/
theorem weight_eq_scoreProbability (temperature : ℝ) (values : J → ℝ) :
    weight temperature values =
      GameTheory.Math.OnlineLearning.scoreProbability temperature⁻¹ values := by
  funext tester
  simp only [weight, partition, GameTheory.Math.OnlineLearning.scoreProbability,
    div_eq_mul_inv, mul_comm]

theorem weight_nonneg (temperature : ℝ) (values : J → ℝ) (tester : J) :
    0 ≤ weight temperature values tester := by
  rw [weight_eq_scoreProbability]
  exact GameTheory.Math.OnlineLearning.scoreProbability_nonneg temperature⁻¹ values tester

theorem sum_weight (temperature : ℝ) (values : J → ℝ) :
    ∑ tester, weight temperature values tester = 1 := by
  rw [weight_eq_scoreProbability]
  exact GameTheory.Math.OnlineLearning.sum_scoreProbability temperature⁻¹ values

theorem value_le_maximum (values : J → ℝ) (tester : J) :
    values tester ≤ maximum values :=
  Finset.le_sup' values (Finset.mem_univ tester)

theorem exists_maximum_tester (values : J → ℝ) :
    ∃ tester, maximum values = values tester := by
  obtain ⟨tester, _, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty values
  exact ⟨tester, heq⟩

omit [Nonempty J] in
theorem value_le_smoothMax {temperature : ℝ} (htemperature : 0 < temperature)
    (values : J → ℝ) (tester : J) :
    values tester ≤ smoothMax temperature values := by
  have hlog := Real.log_le_log (Real.exp_pos _)
    (exp_le_partition temperature values tester)
  rw [Real.log_exp] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog htemperature.le
  have hcancel : temperature * (values tester / temperature) = values tester := by
    field_simp [htemperature.ne']
  simpa only [hcancel, smoothMax] using hscaled

theorem maximum_le_smoothMax {temperature : ℝ} (htemperature : 0 < temperature)
    (values : J → ℝ) :
    maximum values ≤ smoothMax temperature values :=
  Finset.sup'_le Finset.univ_nonempty values
    (fun tester _ => value_le_smoothMax htemperature values tester)

theorem smoothMax_le_maximum_add_log_card {temperature : ℝ}
    (htemperature : 0 < temperature) (values : J → ℝ) :
    smoothMax temperature values ≤ maximum values +
      temperature * Real.log (Fintype.card J : ℝ) := by
  have hcard : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hpartition : partition temperature values ≤
      (Fintype.card J : ℝ) * Real.exp (maximum values / temperature) := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun tester _ =>
      Real.exp_le_exp.mpr
        (div_le_div_of_nonneg_right (value_le_maximum values tester) htemperature.le)
    simpa only [partition, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  have hlog := Real.log_le_log (partition_pos temperature values) hpartition
  rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  calc
    smoothMax temperature values ≤
        temperature * (Real.log (Fintype.card J : ℝ) + maximum values / temperature) :=
      mul_le_mul_of_nonneg_left hlog htemperature.le
    _ = maximum values + temperature * Real.log (Fintype.card J : ℝ) := by
      field_simp [htemperature.ne']
      ring

theorem log_weight (temperature : ℝ) (values : J → ℝ) (tester : J) :
    Real.log (weight temperature values tester) =
      values tester / temperature - Real.log (partition temperature values) := by
  rw [weight, Real.log_div (Real.exp_ne_zero _) (partition_pos temperature values).ne',
    Real.log_exp]

theorem entropy_nonneg (temperature : ℝ) (values : J → ℝ) :
    0 ≤ entropy temperature values :=
  Finset.sum_nonneg fun tester _ =>
    Real.negMulLog_nonneg (weight_pos temperature values tester).le
      (weight_le_one temperature values tester)

/-- Jensen with the uniform law gives the sharp finite entropy ceiling. -/
theorem entropy_le_log_card (temperature : ℝ) (values : J → ℝ) :
    entropy temperature values ≤ Real.log (Fintype.card J : ℝ) := by
  let count : ℝ := Fintype.card J
  have hcount : 0 < count := by
    dsimp only [count]
    exact_mod_cast Fintype.card_pos
  have huniform : (∑ _ : J, (1 / count : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change count * (1 / count) = 1
    field_simp [hcount.ne']
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _ : J => (1 / count : ℝ))
    (p := weight temperature values)
    (fun _ _ => (one_div_pos.mpr hcount).le) huniform
    (fun tester _ => (weight_pos temperature values tester).le)
  have hformula : Real.negMulLog (1 / count) =
      (1 / count) * Real.log count := by
    rw [Real.negMulLog, Real.log_div one_ne_zero hcount.ne', Real.log_one]
    ring
  have hmean : (∑ tester, (1 / count) * weight temperature values tester) = 1 / count := by
    rw [← Finset.mul_sum, sum_weight, mul_one]
  simp only [smul_eq_mul, hmean, hformula] at hjensen
  rw [← Finset.mul_sum] at hjensen
  exact (mul_le_mul_iff_right₀ (one_div_pos.mpr hcount)).mp hjensen

/-- Exact Gibbs entropy identity, not merely the max-approximation bound. -/
theorem smoothMax_eq_weightedMean_add_entropy {temperature : ℝ}
    (htemperature : 0 < temperature) (values : J → ℝ) :
    smoothMax temperature values =
      weightedMean temperature values values + temperature * entropy temperature values := by
  have hterm : ∀ tester,
      weight temperature values tester * values tester +
        temperature * Real.negMulLog (weight temperature values tester) =
      weight temperature values tester * smoothMax temperature values := by
    intro tester
    rw [Real.negMulLog, log_weight, smoothMax]
    field_simp [htemperature.ne']
    ring
  calc
    smoothMax temperature values =
        (∑ tester, weight temperature values tester) * smoothMax temperature values := by
      rw [sum_weight, one_mul]
    _ = ∑ tester, weight temperature values tester * smoothMax temperature values := by
      rw [Finset.sum_mul]
    _ = ∑ tester, (weight temperature values tester * values tester +
        temperature * Real.negMulLog (weight temperature values tester)) :=
      Finset.sum_congr rfl fun tester _ => (hterm tester).symm
    _ = weightedMean temperature values values +
        temperature * entropy temperature values := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl

theorem inactivity_eq (temperature : ℝ) (values : J → ℝ) :
    inactivity temperature values =
      maximum values - weightedMean temperature values values := by
  simp only [inactivity, weightedMean, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_weight, one_mul]

theorem inactivity_nonneg (temperature : ℝ) (values : J → ℝ) :
    0 ≤ inactivity temperature values :=
  Finset.sum_nonneg fun tester _ =>
    mul_nonneg (weight_pos temperature values tester).le
      (sub_nonneg.mpr (value_le_maximum values tester))

theorem inactivity_le_temperature_log_card {temperature : ℝ}
    (htemperature : 0 < temperature) (values : J → ℝ) :
    inactivity temperature values ≤ temperature * Real.log (Fintype.card J : ℝ) := by
  have hmax := maximum_le_smoothMax htemperature values
  rw [smoothMax_eq_weightedMean_add_entropy htemperature values] at hmax
  have hentropy := mul_le_mul_of_nonneg_left (entropy_le_log_card temperature values)
    htemperature.le
  rw [inactivity_eq]
  linarith

/-- A scalar observable averaged under the actual exponential probabilities. -/
theorem partition_mul_weightedMean (temperature : ℝ) (values observable : J → ℝ) :
    partition temperature values * weightedMean temperature values observable =
      ∑ tester, Real.exp (values tester / temperature) * observable tester := by
  rw [weightedMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tester _
  unfold weight
  field_simp [(partition_pos temperature values).ne']

def weightedVariance (temperature : ℝ) (values observable : J → ℝ) : ℝ :=
  ∑ tester, weight temperature values tester *
    (observable tester - weightedMean temperature values observable) ^ 2

theorem weightedVariance_nonneg (temperature : ℝ) (values observable : J → ℝ) :
    0 ≤ weightedVariance temperature values observable :=
  Finset.sum_nonneg fun tester _ =>
    mul_nonneg (weight_pos temperature values tester).le (sq_nonneg _)

theorem weightedVariance_eq (temperature : ℝ) (values observable : J → ℝ) :
    weightedVariance temperature values observable =
      weightedMean temperature values (fun tester => observable tester ^ 2) -
        (weightedMean temperature values observable) ^ 2 := by
  have hterm : ∀ tester,
      weight temperature values tester *
          (observable tester - weightedMean temperature values observable) ^ 2 =
        weight temperature values tester * observable tester ^ 2 -
          (2 * weightedMean temperature values observable) *
            (weight temperature values tester * observable tester) +
          (weightedMean temperature values observable) ^ 2 *
            weight temperature values tester := by
    intro tester
    ring
  unfold weightedVariance
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_weight, mul_one]
  change weightedMean temperature values (fun tester => observable tester ^ 2) -
      2 * weightedMean temperature values observable * weightedMean temperature values observable +
      (weightedMean temperature values observable) ^ 2 =
    weightedMean temperature values (fun tester => observable tester ^ 2) -
      (weightedMean temperature values observable) ^ 2
  ring

theorem sum_centered_mul_eq_variance (temperature : ℝ) (values observable : J → ℝ) :
    (∑ tester, weight temperature values tester *
        (observable tester - weightedMean temperature values observable) * observable tester) =
      weightedVariance temperature values observable := by
  have hterm : ∀ tester,
      weight temperature values tester *
          (observable tester - weightedMean temperature values observable) * observable tester =
        weight temperature values tester * observable tester ^ 2 -
          weightedMean temperature values observable *
            (weight temperature values tester * observable tester) := by
    intro tester
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, weightedVariance_eq]
  change weightedMean temperature values (fun tester => observable tester ^ 2) -
      weightedMean temperature values observable * weightedMean temperature values observable =
    weightedMean temperature values (fun tester => observable tester ^ 2) -
      (weightedMean temperature values observable) ^ 2
  ring

theorem weightedMean_le (temperature : ℝ) (values observable : J → ℝ) (bound : ℝ)
    (hbound : ∀ tester, observable tester ≤ bound) :
    weightedMean temperature values observable ≤ bound := by
  calc
    weightedMean temperature values observable ≤
        ∑ tester, weight temperature values tester * bound :=
      Finset.sum_le_sum fun tester _ =>
        mul_le_mul_of_nonneg_left (hbound tester) (weight_pos temperature values tester).le
    _ = bound := by rw [← Finset.sum_mul, sum_weight, one_mul]

theorem weightedVariance_le_sq (temperature : ℝ) (values observable : J → ℝ) (bound : ℝ)
    (hbound : ∀ tester, |observable tester| ≤ bound) :
    weightedVariance temperature values observable ≤ bound ^ 2 := by
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg (observable (Classical.arbitrary J))).trans (hbound _)
  have hsq : ∀ tester, observable tester ^ 2 ≤ bound ^ 2 := by
    intro tester
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (observable tester)) hbound0).mpr (hbound tester)
  have hmean := weightedMean_le temperature values (fun tester => observable tester ^ 2)
    (bound ^ 2) hsq
  rw [weightedVariance_eq]
  linarith [sq_nonneg (weightedMean temperature values observable)]

/-- The partition derivative uses only component derivatives at this one point. -/
theorem partition_hasDerivAt (temperature : ℝ) (curves : J → ℝ → ℝ)
    (slopes : J → ℝ) (point : ℝ) (hcurves : ∀ tester,
      HasDerivAt (curves tester) (slopes tester) point) :
    HasDerivAt (fun time => partition temperature (fun tester => curves tester time))
      (partition temperature (fun tester => curves tester point) *
        weightedMean temperature (fun tester => curves tester point) slopes / temperature)
      point := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun tester _ => ((hcurves tester).div_const temperature).exp)
  have hslope :
      (∑ tester, Real.exp (curves tester point / temperature) *
          (slopes tester / temperature)) =
        partition temperature (fun tester => curves tester point) *
          weightedMean temperature (fun tester => curves tester point) slopes / temperature := by
    rw [partition_mul_weightedMean, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro tester _
    ring
  exact hsum.congr_deriv hslope

theorem smoothMax_hasDerivAt {temperature : ℝ} (htemperature : 0 < temperature)
    (curves : J → ℝ → ℝ) (slopes : J → ℝ) (point : ℝ)
    (hcurves : ∀ tester, HasDerivAt (curves tester) (slopes tester) point) :
    HasDerivAt (fun time => smoothMax temperature (fun tester => curves tester time))
      (weightedMean temperature (fun tester => curves tester point) slopes) point := by
  have hpartition := partition_hasDerivAt temperature curves slopes point hcurves
  have hlog := (hpartition.log
    (partition_pos temperature (fun tester => curves tester point)).ne').const_mul temperature
  have hslope : temperature *
      ((partition temperature (fun tester => curves tester point) *
        weightedMean temperature (fun tester => curves tester point) slopes / temperature) /
          partition temperature (fun tester => curves tester point)) =
      weightedMean temperature (fun tester => curves tester point) slopes := by
    field_simp [htemperature.ne',
      (partition_pos temperature (fun tester => curves tester point)).ne']
  exact hlog.congr_deriv hslope

theorem deriv_smoothMax {temperature : ℝ} (htemperature : 0 < temperature)
    (curves : J → ℝ → ℝ) (point : ℝ)
    (hcurves : ∀ tester, DifferentiableAt ℝ (curves tester) point) :
    deriv (fun time => smoothMax temperature (fun tester => curves tester time)) point =
      weightedMean temperature (fun tester => curves tester point)
        (fun tester => deriv (curves tester) point) :=
  (smoothMax_hasDerivAt htemperature curves _ point
    (fun tester => (hcurves tester).hasDerivAt)).deriv

theorem weight_hasDerivAt {temperature : ℝ} (htemperature : 0 < temperature)
    (curves : J → ℝ → ℝ) (slopes : J → ℝ) (point : ℝ)
    (hcurves : ∀ tester, HasDerivAt (curves tester) (slopes tester) point) (tester : J) :
    HasDerivAt (fun time => weight temperature (fun other => curves other time) tester)
      (weight temperature (fun other => curves other point) tester *
        (slopes tester - weightedMean temperature (fun other => curves other point) slopes) /
          temperature) point := by
  have hpartition := partition_hasDerivAt temperature curves slopes point hcurves
  have hquotient := ((hcurves tester).div_const temperature).exp.fun_div hpartition
    (partition_pos temperature (fun other => curves other point)).ne'
  have hslope :
      (Real.exp (curves tester point / temperature) * (slopes tester / temperature) *
          partition temperature (fun other => curves other point) -
        Real.exp (curves tester point / temperature) *
          (partition temperature (fun other => curves other point) *
            weightedMean temperature (fun other => curves other point) slopes / temperature)) /
            (partition temperature (fun other => curves other point)) ^ 2 =
        weight temperature (fun other => curves other point) tester *
          (slopes tester - weightedMean temperature (fun other => curves other point) slopes) /
            temperature := by
    unfold weight
    field_simp [htemperature.ne',
      (partition_pos temperature (fun other => curves other point)).ne']
  exact hquotient.congr_deriv hslope

/-- The derivative of the weighted actual first derivatives, with no global C2 premise. -/
theorem weightedDerivative_hasDerivAt {temperature : ℝ} (htemperature : 0 < temperature)
    (curves : J → ℝ → ℝ) (point : ℝ)
    (hfirst : ∀ tester, DifferentiableAt ℝ (curves tester) point)
    (hsecond : ∀ tester, DifferentiableAt ℝ (deriv (curves tester)) point) :
    HasDerivAt (fun time => weightedMean temperature (fun tester => curves tester time)
      (fun tester => deriv (curves tester) time))
      (weightedMean temperature (fun tester => curves tester point)
          (fun tester => deriv (deriv (curves tester)) point) +
        weightedVariance temperature (fun tester => curves tester point)
          (fun tester => deriv (curves tester) point) / temperature) point := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun tester _ =>
    (weight_hasDerivAt htemperature curves _ point
      (fun other => (hfirst other).hasDerivAt) tester).mul (hsecond tester).hasDerivAt)
  have hterm : ∀ tester,
      (weight temperature (fun other => curves other point) tester *
          (deriv (curves tester) point -
            weightedMean temperature (fun other => curves other point)
              (fun other => deriv (curves other) point)) / temperature) *
            deriv (curves tester) point +
          weight temperature (fun other => curves other point) tester *
            deriv (deriv (curves tester)) point =
        weight temperature (fun other => curves other point) tester *
            deriv (deriv (curves tester)) point +
          (weight temperature (fun other => curves other point) tester *
            (deriv (curves tester) point -
              weightedMean temperature (fun other => curves other point)
                (fun other => deriv (curves other) point)) * deriv (curves tester) point) /
            temperature := by
    intro tester
    ring
  have hslope :
      (∑ tester,
        ((weight temperature (fun other => curves other point) tester *
            (deriv (curves tester) point -
              weightedMean temperature (fun other => curves other point)
                (fun other => deriv (curves other) point)) / temperature) *
              deriv (curves tester) point +
            weight temperature (fun other => curves other point) tester *
              deriv (deriv (curves tester)) point)) =
        weightedMean temperature (fun tester => curves tester point)
            (fun tester => deriv (deriv (curves tester)) point) +
          weightedVariance temperature (fun tester => curves tester point)
            (fun tester => deriv (curves tester) point) / temperature := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, sum_centered_mul_eq_variance]
    rfl
  exact hsum.congr_deriv hslope

/-- The literal second derivative: weighted component curvature plus variance/temperature.
Only local C2 at the queried point is required. -/
theorem deriv_smoothMax_hasDerivAt {temperature : ℝ} (htemperature : 0 < temperature)
    (curves : J → ℝ → ℝ) (point : ℝ)
    (hcurves : ∀ tester, ContDiffAt ℝ 2 (curves tester) point) :
    HasDerivAt (deriv (fun time =>
      smoothMax temperature (fun tester => curves tester time)))
      (weightedMean temperature (fun tester => curves tester point)
          (fun tester => deriv (deriv (curves tester)) point) +
        weightedVariance temperature (fun tester => curves tester point)
          (fun tester => deriv (curves tester) point) / temperature) point := by
  have hfirst : ∀ tester, DifferentiableAt ℝ (curves tester) point :=
    fun tester => (hcurves tester).differentiableAt (by norm_num)
  have hsecond : ∀ tester, DifferentiableAt ℝ (deriv (curves tester)) point := by
    intro tester
    have hderiv : ContDiffAt ℝ 1 (deriv (curves tester)) point :=
      (hcurves tester).derivWithin (by norm_num)
    exact hderiv.differentiableAt_one
  have hweighted := weightedDerivative_hasDerivAt htemperature curves point hfirst hsecond
  have hlocal : ∀ᶠ time in 𝓝 point, ∀ tester,
      DifferentiableAt ℝ (curves tester) time := by
    apply Filter.eventually_all.mpr
    intro tester
    filter_upwards [(hcurves tester).eventually (by norm_num)] with time htime
    exact htime.differentiableAt (by norm_num)
  have heq :
      deriv (fun time => smoothMax temperature (fun tester => curves tester time)) =ᶠ[𝓝 point]
      (fun time => weightedMean temperature (fun tester => curves tester time)
        (fun tester => deriv (curves tester) time)) :=
    hlocal.mono fun time htime => deriv_smoothMax htemperature curves time htime
  exact hweighted.congr_of_eventuallyEq heq

theorem deriv2_smoothMax {temperature : ℝ} (htemperature : 0 < temperature)
    (curves : J → ℝ → ℝ) (point : ℝ)
    (hcurves : ∀ tester, ContDiffAt ℝ 2 (curves tester) point) :
    deriv (deriv (fun time => smoothMax temperature (fun tester => curves tester time))) point =
      weightedMean temperature (fun tester => curves tester point)
          (fun tester => deriv (deriv (curves tester)) point) +
        weightedVariance temperature (fun tester => curves tester point)
          (fun tester => deriv (curves tester) point) / temperature :=
  (deriv_smoothMax_hasDerivAt htemperature curves point hcurves).deriv

theorem deriv2_smoothMax_le {temperature : ℝ} (htemperature : 0 < temperature)
    (curves : J → ℝ → ℝ) (point firstBound secondBound : ℝ)
    (hcurves : ∀ tester, ContDiffAt ℝ 2 (curves tester) point)
    (hfirstBound : ∀ tester, |deriv (curves tester) point| ≤ firstBound)
    (hsecondBound : ∀ tester, deriv (deriv (curves tester)) point ≤ secondBound) :
    deriv (deriv (fun time => smoothMax temperature (fun tester => curves tester time))) point ≤
      secondBound + firstBound ^ 2 / temperature := by
  rw [deriv2_smoothMax htemperature curves point hcurves]
  exact add_le_add
    (weightedMean_le temperature (fun tester => curves tester point) _ secondBound hsecondBound)
    (div_le_div_of_nonneg_right
      (weightedVariance_le_sq temperature (fun tester => curves tester point) _
        firstBound hfirstBound) htemperature.le)

end Math.FiniteLogSumExp
