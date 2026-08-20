/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Fink.LimitStationary
import MathUE.CalendarSummability

/-!
# Scheduled corrected-target Fink calculus

Adjacent-correction identities, correction error budgets, scheduled
state-value transport, target-average bounds, and the corrected-target
uniform-equilibrium compiler.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter
open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- Exact on-profile one-step decomposition for adjacent corrections.  The
defect is the same-index continuation residual plus the continuation value of
the correction increment. -/
theorem fink_correctedTarget_onProfile_step_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) :
    expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) -
      (W s who + R₀ s who) =
    G.finkContinuationResidual (W + R₀) z s who +
      G.finkContinuationEU (R₁ - R₀) z s who := by
  change G.finkContinuationEU (W + R₁) z s who -
      (W + R₀) s who = _
  rw [show W + R₁ = (W + R₀) + (R₁ - R₀) by abel]
  rw [G.finkContinuationEU_add]
  simp only [finkContinuationResidual, Pi.add_apply]
  ring

/-- Exact pure-deviation analogue of
`fink_correctedTarget_onProfile_step_eq`. -/
theorem fink_correctedTarget_pureDeviation_step_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι)
    (d : G.Act who) :
    expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) -
        (W s who + R₀ s who) =
      G.finkContinuationResidual (W + R₀) z s who +
        G.finkContinuationGain (W + R₀) z s who d +
        expect (pmfPi (Function.update (G.finkProfile z s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => (R₁ - R₀) s' who)) := by
  change (expect (pmfPi (Function.update (G.finkProfile z s)
      who (PMF.pure d))) (fun a =>
    expect (G.transition s a) (fun s' => (W + R₁) s' who))) -
      (W + R₀) s who = _
  rw [show W + R₁ = (W + R₀) + (R₁ - R₀) by abel]
  unfold finkContinuationResidual finkContinuationGain finkContinuationEU
  simp_rw [Pi.add_apply, expect_add]
  ring

/-- Same-index harmonic error and adjacent correction motion jointly bound
the on-profile time-dependent potential step. -/
theorem abs_fink_correctedTarget_onProfile_step_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (r m : ℝ)
    (hresidual : |G.finkContinuationResidual (W + R₀) z s who| ≤ r)
    (hmove : ∀ s', |(R₁ - R₀) s' who| ≤ m) :
    |expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) -
      (W s who + R₀ s who)| ≤ r + m := by
  rw [G.fink_correctedTarget_onProfile_step_eq W R₀ R₁ z s who]
  have hcontinuation :
      |G.finkContinuationEU (R₁ - R₀) z s who| ≤ m := by
    unfold finkContinuationEU
    exact abs_expect_le_of_abs_le _ _ fun a =>
      abs_expect_le_of_abs_le _ _ hmove
  exact (abs_add_le _ _).trans (add_le_add hresidual hcontinuation)

/-- Pure gain bounds lift to arbitrary mixed deviations after adding the
same-index residual and adjacent correction-motion charges. -/
theorem fink_correctedTarget_mixedDeviation_step_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W R₀ R₁ : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι)
    (r g m : ℝ)
    (hresidual : G.finkContinuationResidual (W + R₀) z s who ≤ r)
    (hgain : ∀ d : G.Act who,
      G.finkContinuationGain (W + R₀) z s who d ≤ g)
    (hmove : ∀ s', |(R₁ - R₀) s' who| ≤ m)
    (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (G.finkProfile z s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who + R₁ s' who)) ≤
      W s who + R₀ s who + (r + g + m) := by
  apply G.mixedDeviationContinuation_le_of_pure_bound
    (G.finkProfile z) (W + R₁) s who
      (W s who + R₀ s who + (r + g + m))
  intro d
  have hmovePure :
      expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => (R₁ - R₀) s' who)) ≤ m := by
    exact (le_abs_self _).trans (abs_expect_le_of_abs_le _ _ fun a =>
      abs_expect_le_of_abs_le _ _ hmove)
  have hdecomp :=
    G.fink_correctedTarget_pureDeviation_step_eq W R₀ R₁ z s who d
  simp only [Pi.add_apply] at ⊢
  linarith [hgain d]

/-- Finite sum of the positive pure-deviation continuation gains of a
potential.  Using a sum rather than a maximum also covers degenerate empty
coordinate types without extra inhabitedness assumptions. -/
noncomputable def finkPositiveContinuationGainSum
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (C : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) : ℝ :=
  ∑ p : G.FinkPureActionIndex,
    max (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0

theorem finkContinuationGain_le_positiveSum
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (C : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain C z s who d ≤
      G.finkPositiveContinuationGainSum C z := by
  classical
  let q : G.FinkPureActionIndex := ⟨s, ⟨who, d⟩⟩
  calc
    G.finkContinuationGain C z s who d ≤
        max (G.finkContinuationGain C z s who d) 0 := le_max_left _ _
    _ ≤ ∑ p : G.FinkPureActionIndex,
        max (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0 := by
      let f : G.FinkPureActionIndex → ℝ := fun p =>
        max (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0
      change f q ≤ ∑ p, f p
      exact Finset.single_le_sum
        (fun p _ => le_max_right
          (G.finkContinuationGain C z p.1 p.2.1 p.2.2) 0)
        (Finset.mem_univ q)
    _ = G.finkPositiveContinuationGainSum C z := rfl

/-- One scalar charges all defects in an adjacent corrected-target step:
same-index harmonic residual, positive pure-deviation gain, and correction
motion. -/
noncomputable def finkCorrectedTargetStepError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) : ℝ :=
  ‖G.finkContinuationResidualVector (W + R t) (z t)‖ +
    G.finkPositiveContinuationGainSum (W + R t) (z t) +
    ‖R (t + 1) - R t‖

theorem finkCorrectedTargetStepError_nonneg
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ) :
    0 ≤ G.finkCorrectedTargetStepError W R z t := by
  unfold finkCorrectedTargetStepError finkPositiveContinuationGainSum
  positivity

/-- A nonzero first-order continuation residual cannot be hidden by a
zero-correction annealing calendar whose bias scale is negligible relative to
calendar time.  The residual forces at least harmonic-series hold cost, so
the summable-drift verification route is genuinely unavailable on this
branch. -/
theorem not_summable_zeroCorrectionStepError_of_scaledResidual_tendsto_ne_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (z : ℕ → G.finkDomain U) (W F : G.State → Payoff ι)
    (hscaled : Tendsto (fun n =>
      a n • G.finkContinuationResidualVector W (z n))
        atTop (nhds F))
    (hF : F ≠ 0) (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hterminal : Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ * a (κ T)) atTop (nhds 0)) :
    ¬ Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t) := by
  let e : ℕ → ℝ := fun t => G.finkCorrectedTargetStepError W
    ((fun _ => 0) ∘ κ) (z ∘ κ) t
  let c : ℝ := ‖F‖ / 2
  have hc : 0 < c := by
    dsimp only [c]
    exact half_pos (norm_pos_iff.mpr hF)
  have hnorm : Tendsto (fun t =>
      ‖a (κ t) • G.finkContinuationResidualVector W (z (κ t))‖)
      atTop (nhds ‖F‖) := by
    simpa only [Function.comp_apply] using (hscaled.comp hκ).norm
  have hlowerNorm : ∀ᶠ t : ℕ in atTop,
      c ≤ ‖a (κ t) •
        G.finkContinuationResidualVector W (z (κ t))‖ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm c hc
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with t ht
    rw [Real.dist_eq, abs_lt] at ht
    dsimp only [c] at ht ⊢
    linarith
  have he0 : ∀ t, 0 ≤ e t := fun t =>
    G.finkCorrectedTargetStepError_nonneg W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t
  have hlower : ∀ᶠ t : ℕ in atTop, c ≤ a (κ t) * e t := by
    filter_upwards [hlowerNorm] with t ht
    have hstep : ‖G.finkContinuationResidualVector W (z (κ t))‖ ≤ e t := by
      dsimp only [e]
      unfold finkCorrectedTargetStepError
      simp only [Function.comp_apply, add_zero, sub_self,
        norm_zero, add_zero]
      apply le_add_of_nonneg_right
      unfold finkPositiveContinuationGainSum
      exact Finset.sum_nonneg fun p hp => le_max_right _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha0 (κ t))] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hstep (ha0 (κ t)))
  exact Math.CalendarSummability.not_summable_of_eventually_pos_le_mul_of_inv_mul_tendsto_zero
    (a ∘ κ) e c hc he0 hlower (by
      simpa only [Function.comp_apply] using hterminal)

/-- Concrete finite-bias no-go theorem.  If the limiting Bellman forcing is
nonzero, every zero-correction calendar that amortizes the scaled discounted
bias necessarily has nonsummable corrected-target drift. -/
theorem not_summable_zeroCorrectionStepError_of_finkBellmanForcing_ne_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℕ → ℝ) (U : ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hforcing : G.finkBellmanForcingVector W H zlim ≠ 0)
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      (β (κ T) / (1 - β (κ T)))) atTop (nhds 0)) :
    ¬ Summable (fun t => G.finkCorrectedTargetStepError W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t) := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkRelativeBias (β n) W (z n)
  let E : ℕ → G.State → Payoff ι := fun n =>
    G.finkContinuationResidualVector W (z n)
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    div_nonneg (hβ0 n) (sub_nonneg.mpr (hβ1 n).le)
  have hbellman : ∀ n s who,
      G.finkValue (z n) s who + J n s who =
        G.finkStageEU (z n) s who +
          G.finkContinuationEU (J n) (z n) s who +
            a n * E n s who := by
    intro n s who
    simpa only [J, E, a, finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  have hscaled := G.tendsto_smul_finkBellmanForcingVector hz hV
    (by simpa only [J] using hH) a hbellman
  apply G.not_summable_zeroCorrectionStepError_of_scaledResidual_tendsto_ne_zero
    a ha0 z W (G.finkBellmanForcingVector W H zlim) hscaled hforcing
      κ hκ
  simpa only [a] using hterminal

/-- Strong zero-correction calendar no-go theorem.  Under nonzero limiting
Bellman forcing, the exact normalized cumulative-drift bill appearing in
`IsIndexedFinkCorrectedCalendarSelectable` is unbounded along every
cofinal bias-amortizing calendar. -/
theorem not_eventually_bounded_zeroCorrectionCumulativeDrift_of_finkBellmanForcing_ne_zero
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℕ → ℝ) (U : ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hforcing : G.finkBellmanForcingVector W H zlim ≠ 0)
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hterminal : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ *
      (β (κ T) / (1 - β (κ T)))) atTop (nhds 0)) :
    ¬ ∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.range t,
          G.finkCorrectedTargetStepError W
            ((fun _ => 0) ∘ κ) (z ∘ κ) k ≤ C := by
  rintro ⟨C, hC⟩
  let e : ℕ → ℝ := fun t => G.finkCorrectedTargetStepError W
    ((fun _ => 0) ∘ κ) (z ∘ κ) t
  have he0 : ∀ t, 0 ≤ e t := fun t =>
    G.finkCorrectedTargetStepError_nonneg W
      ((fun _ => 0) ∘ κ) (z ∘ κ) t
  have heSummable : Summable e :=
    Math.CalendarSummability.summable_of_eventually_normalized_cumulative_sum_le e he0 C
      (by simpa only [e] using hC)
  have heNotSummable :=
    G.not_summable_zeroCorrectionStepError_of_finkBellmanForcing_ne_zero
      β U hβ0 hβ1 hpay z zlim W H hfix hz hV hH hforcing
        κ hκ hterminal
  exact heNotSummable (by simpa only [e] using heSummable)

/-- The canonical corrected-target error controls the on-profile step in the
exact form consumed by the time-dependent potential telescope. -/
theorem abs_fink_correctedTarget_onProfile_step_le_stepError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ)
    (s : G.State) (who : ι) :
    |expect (pmfPi (G.finkProfile (z t) s)) (fun a =>
        expect (G.transition s a)
          (fun s' => W s' who + R (t + 1) s' who)) -
      (W s who + R t s who)| ≤
        G.finkCorrectedTargetStepError W R z t := by
  have hresidual :
      |G.finkContinuationResidual (W + R t) (z t) s who| ≤
        ‖G.finkContinuationResidualVector (W + R t) (z t)‖ := by
    exact G.abs_finkBiasCoordinate_le_norm
      (G.finkContinuationResidualVector (W + R t) (z t)) s who
  have hmove : ∀ s', |(R (t + 1) - R t) s' who| ≤
      ‖R (t + 1) - R t‖ := fun s' =>
    G.abs_finkBiasCoordinate_le_norm (R (t + 1) - R t) s' who
  have hstep := G.abs_fink_correctedTarget_onProfile_step_le
    W (R t) (R (t + 1)) (z t) s who
      ‖G.finkContinuationResidualVector (W + R t) (z t)‖
      ‖R (t + 1) - R t‖ hresidual hmove
  have hgainNonneg : 0 ≤
      G.finkPositiveContinuationGainSum (W + R t) (z t) := by
    unfold finkPositiveContinuationGainSum
    exact Finset.sum_nonneg fun p _ => le_max_right _ _
  exact hstep.trans (by
    unfold finkCorrectedTargetStepError
    linarith)

/-- The same canonical error controls every mixed unilateral deviation, and
hence every history-dependent deviation after the telescope. -/
theorem fink_correctedTarget_mixedDeviation_step_le_stepError
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [DecidableEq ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) (R : ℕ → G.State → Payoff ι)
    {U : ℝ} (z : ℕ → G.finkDomain U) (t : ℕ)
    (s : G.State) (who : ι) (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (G.finkProfile (z t) s) who dev))
        (fun a => expect (G.transition s a)
          (fun s' => W s' who + R (t + 1) s' who)) ≤
      W s who + R t s who + G.finkCorrectedTargetStepError W R z t := by
  apply G.fink_correctedTarget_mixedDeviation_step_le
    W (R t) (R (t + 1)) (z t) s who
      ‖G.finkContinuationResidualVector (W + R t) (z t)‖
      (G.finkPositiveContinuationGainSum (W + R t) (z t))
      ‖R (t + 1) - R t‖
  · exact (le_abs_self _).trans
      (G.abs_finkBiasCoordinate_le_norm
        (G.finkContinuationResidualVector (W + R t) (z t)) s who)
  · intro d
    exact G.finkContinuationGain_le_positiveSum (W + R t) (z t) s who d
  · intro s'
    exact G.abs_finkBiasCoordinate_le_norm (R (t + 1) - R t) s' who

/-- A time-dependent state potential telescopes along a scheduled Markov
profile.  Unlike a pointwise bound on the drift of one fixed target, this
form retains cancellations supplied by Poisson corrections. -/
theorem scheduled_expectedTimeDependentStateValue_close_initial
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (C : ℕ → G.State → Payoff ι) (r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a) (fun s' => C (t + 1) s' who)) -
        C t s who| ≤ r t)
    (T : ℕ) :
    |G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ T
        (fun s => C T s who) - C 0 s₀ who| ≤
      ∑ t ∈ Finset.range T, r t := by
  let σ := G.scheduledMarkovBehaviorProfile x
  let A : ℕ → ℝ := fun t =>
    G.expectedStateValue σ s₀ t (fun s => C t s who)
  have hA : ∀ T, |A T - A 0| ≤ ∑ t ∈ Finset.range T, r t := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have hup : A (N + 1) ≤ A N + r N := by
          rw [show A (N + 1) = G.expectedStateValue σ s₀ (N + 1)
              (fun s => C (N + 1) s who) from rfl,
            G.expectedStateValue_succ]
          calc
            expect (G.histDist σ s₀ N) (fun h =>
                expect (G.stageActionDist σ h) (fun a =>
                  expect (G.transition h.2 a)
                    (fun s' => C (N + 1) s' who))) ≤
              expect (G.histDist σ s₀ N)
                (fun h => C N h.2 who + r N) := by
              apply expect_mono
              intro h
              rw [show G.stageActionDist σ h = pmfPi (x N h.2) from rfl]
              have hh := (abs_le.mp (hstep N h.2)).2
              linarith
            _ = A N + r N := by
              rw [expect_add, expect_const]
              rfl
        have hlo : A N ≤ A (N + 1) + r N := by
          calc
            A N = expect (G.histDist σ s₀ N)
                (fun h => C N h.2 who) := rfl
            _ ≤ expect (G.histDist σ s₀ N) (fun h =>
                expect (G.stageActionDist σ h) (fun a =>
                  expect (G.transition h.2 a)
                    (fun s' => C (N + 1) s' who)) + r N) := by
              apply expect_mono
              intro h
              rw [show G.stageActionDist σ h = pmfPi (x N h.2) from rfl]
              have hh := (abs_le.mp (hstep N h.2)).1
              linarith
            _ = A (N + 1) + r N := by
              rw [expect_add, expect_const]
              change _ = G.expectedStateValue σ s₀ (N + 1)
                (fun s => C (N + 1) s who) + r N
              rw [G.expectedStateValue_succ]
        have hone : |A (N + 1) - A N| ≤ r N :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        have htriangle : |A (N + 1) - A 0| ≤
            |A (N + 1) - A N| + |A N - A 0| := by
          calc
            |A (N + 1) - A 0| =
                |(A (N + 1) - A N) + (A N - A 0)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        rw [Finset.sum_range_succ]
        linarith
  simpa only [A, σ, G.expectedStateValue_zero] using hA T

/-- Deviation-side time-dependent potential telescope.  A one-step
superharmonic correction remains valid against an arbitrary history-dependent
unilateral deviation. -/
theorem scheduled_deviation_expectedTimeDependentStateValue_le_initial
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (C : ℕ → G.State → Payoff ι) (r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a) (fun s' => C (t + 1) s' who)) ≤
        C t s who + r t)
    (T : ℕ) :
    G.expectedStateValue
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
        s₀ T (fun s => C T s who) ≤
      C 0 s₀ who + ∑ t ∈ Finset.range T, r t := by
  induction T with
  | zero => simp
  | succ T ih =>
      let σ := Function.update (G.scheduledMarkovBehaviorProfile x) who dev
      have hone : G.expectedStateValue σ s₀ (T + 1)
          (fun s => C (T + 1) s who) ≤
          G.expectedStateValue σ s₀ T (fun s => C T s who) + r T := by
        rw [G.expectedStateValue_succ]
        calc
          expect (G.histDist σ s₀ T) (fun h =>
              expect (G.stageActionDist σ h) (fun a =>
                expect (G.transition h.2 a)
                  (fun s' => C (T + 1) s' who))) ≤
            expect (G.histDist σ s₀ T)
              (fun h => C T h.2 who + r T) := by
              apply expect_mono
              intro h
              rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
              exact hstep T h.2 (dev T h)
          _ = G.expectedStateValue σ s₀ T
              (fun s => C T s who) + r T := by
            rw [expect_add, expect_const]
            rfl
      rw [Finset.sum_range_succ]
      linarith

/-- A bounded time-dependent correction converts the potential telescope
into control of the original target.  The correction is paid only at the two
endpoints, not once per calendar stage. -/
theorem scheduled_expectedStateValue_close_initial_of_correction
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (c r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) -
        (W s who + R t s who)| ≤ r t)
    (T : ℕ) :
    |G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ T
        (fun s => W s who) - W s₀ who| ≤
      c 0 + c T + ∑ t ∈ Finset.range T, r t := by
  let σ := G.scheduledMarkovBehaviorProfile x
  let C : ℕ → G.State → Payoff ι :=
    fun t s i => W s i + R t s i
  have hC := G.scheduled_expectedTimeDependentStateValue_close_initial
    x C r who s₀ (by
      intro t s
      simpa only [C] using hstep t s) T
  have hdecomp : G.expectedStateValue σ s₀ T
      (fun s => C T s who) =
      G.expectedStateValue σ s₀ T (fun s => W s who) +
        G.expectedStateValue σ s₀ T (fun s => R T s who) := by
    unfold expectedStateValue
    rw [expect_add]
  have hRT : |G.expectedStateValue σ s₀ T
      (fun s => R T s who)| ≤ c T := by
    unfold expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun h => hR T h.2
  have hR0 := hR 0 s₀
  have htriangle :
      |G.expectedStateValue σ s₀ T (fun s => W s who) - W s₀ who| ≤
        |G.expectedStateValue σ s₀ T (fun s => C T s who) -
          C 0 s₀ who| + |R 0 s₀ who| +
            |G.expectedStateValue σ s₀ T (fun s => R T s who)| := by
    rw [hdecomp]
    dsimp only [C]
    let a := (G.expectedStateValue σ s₀ T (fun s => W s who) +
      G.expectedStateValue σ s₀ T (fun s => R T s who)) -
        (W s₀ who + R 0 s₀ who)
    let b := R 0 s₀ who
    let d := G.expectedStateValue σ s₀ T (fun s => R T s who)
    change |(G.expectedStateValue σ s₀ T (fun s => W s who) -
      W s₀ who)| ≤ |a| + |b| + |d|
    have heq : G.expectedStateValue σ s₀ T (fun s => W s who) -
        W s₀ who = a + b - d := by
      dsimp only [a, b, d]
      ring
    rw [heq]
    calc
      |a + b - d| = |(a + b) + (-d)| := by ring_nf
      _ ≤ |a + b| + |-d| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |d| := by
        rw [abs_neg]
        exact add_le_add (abs_add_le _ _) le_rfl
  exact htriangle.trans (by linarith)

/-- Deviation-side corrected-potential estimate.  A bounded correction is
again charged only at the endpoints. -/
theorem scheduled_deviation_expectedStateValue_le_initial_of_correction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (c r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) ≤
        W s who + R t s who + r t)
    (T : ℕ) :
    G.expectedStateValue
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
        s₀ T (fun s => W s who) ≤
      W s₀ who + c 0 + c T + ∑ t ∈ Finset.range T, r t := by
  let σ := Function.update (G.scheduledMarkovBehaviorProfile x) who dev
  let C : ℕ → G.State → Payoff ι :=
    fun t s i => W s i + R t s i
  have hC :=
    G.scheduled_deviation_expectedTimeDependentStateValue_le_initial
      x C r who dev s₀ (by
        intro t s d
        simpa only [C, add_assoc] using hstep t s d) T
  have hdecomp : G.expectedStateValue σ s₀ T
      (fun s => C T s who) =
      G.expectedStateValue σ s₀ T (fun s => W s who) +
        G.expectedStateValue σ s₀ T (fun s => R T s who) := by
    unfold expectedStateValue
    rw [expect_add]
  have hRT : |G.expectedStateValue σ s₀ T
      (fun s => R T s who)| ≤ c T := by
    unfold expectedStateValue
    exact abs_expect_le_of_abs_le _ _ fun h => hR T h.2
  have hR0 := hR 0 s₀
  rw [hdecomp] at hC
  dsimp only [C] at hC
  linarith [neg_abs_le (G.expectedStateValue σ s₀ T
    (fun s => R T s who)), le_abs_self (R 0 s₀ who)]

/-- Scheduled certificate values close to a target inherit the corrected
potential estimate. -/
theorem scheduled_expectedTarget_close_initial_of_correction
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) -
        (W s who + R t s who)| ≤ r t)
    (T : ℕ) :
    |G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ T
        (fun s => V T s who) - W s₀ who| ≤
      q T + c 0 + c T + ∑ t ∈ Finset.range T, r t := by
  let σ := G.scheduledMarkovBehaviorProfile x
  have hVW :
      |G.expectedStateValue σ s₀ T (fun s => V T s who) -
        G.expectedStateValue σ s₀ T (fun s => W s who)| ≤ q T := by
    unfold expectedStateValue
    rw [← expect_sub]
    exact abs_expect_le_of_abs_le _ _ fun h => hclose T h.2
  have hW := G.scheduled_expectedStateValue_close_initial_of_correction
    x W R c r who s₀ hR hstep T
  have htriangle :
      |G.expectedStateValue σ s₀ T (fun s => V T s who) - W s₀ who| ≤
        |G.expectedStateValue σ s₀ T (fun s => V T s who) -
          G.expectedStateValue σ s₀ T (fun s => W s who)| +
        |G.expectedStateValue σ s₀ T (fun s => W s who) - W s₀ who| := by
    calc
      |_ - _| = |(_ - G.expectedStateValue σ s₀ T
          (fun s => W s who)) +
          (G.expectedStateValue σ s₀ T (fun s => W s who) -
            W s₀ who)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith

/-- Deviation-side certificate estimate with a bounded Poisson correction. -/
theorem scheduled_deviation_expectedTarget_le_initial_of_correction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) ≤
        W s who + R t s who + r t)
    (T : ℕ) :
    G.expectedStateValue
        (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
        s₀ T (fun s => V T s who) ≤
      W s₀ who + q T + c 0 + c T +
        ∑ t ∈ Finset.range T, r t := by
  let σ := Function.update (G.scheduledMarkovBehaviorProfile x) who dev
  have hVW : G.expectedStateValue σ s₀ T (fun s => V T s who) ≤
      G.expectedStateValue σ s₀ T (fun s => W s who) + q T := by
    calc
      G.expectedStateValue σ s₀ T (fun s => V T s who) ≤
          expect (G.histDist σ s₀ T) (fun h => W h.2 who + q T) := by
        apply expect_mono
        intro h
        have hh := (abs_le.mp (hclose T h.2)).2
        linarith
      _ = G.expectedStateValue σ s₀ T (fun s => W s who) + q T := by
        rw [expect_add, expect_const]
        rfl
  have hW :=
    G.scheduled_deviation_expectedStateValue_le_initial_of_correction
      x W R c r who dev s₀ hR hstep T
  linarith

/-- Average on-path target estimate retaining time-dependent Poisson
corrections. -/
theorem scheduled_targetAverage_close_initial_of_correction
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s,
      |expect (pmfPi (x t s)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) -
        (W s who + R t s who)| ≤ r t)
    {T : ℕ} (hT : 0 < T) :
    |(T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ t
            (fun s => V t s who) - W s₀ who| ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q t + c 0 + c t + ∑ k ∈ Finset.range t, r k) := by
  let A : ℕ → ℝ := fun t =>
    G.expectedStateValue (G.scheduledMarkovBehaviorProfile x) s₀ t
      (fun s => V t s who)
  let E : ℕ → ℝ := fun t =>
    q t + c 0 + c t + ∑ k ∈ Finset.range t, r k
  have hpoint : ∀ t, |A t - W s₀ who| ≤ E t := fun t =>
    G.scheduled_expectedTarget_close_initial_of_correction
      x V W R q c r who s₀ hclose hR hstep t
  have hsum : |∑ t ∈ Finset.range T, (A t - W s₀ who)| ≤
      ∑ t ∈ Finset.range T, E t := by
    calc
      |∑ t ∈ Finset.range T, (A t - W s₀ who)| ≤
          ∑ t ∈ Finset.range T, |A t - W s₀ who| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range T, E t :=
        Finset.sum_le_sum fun t _ => hpoint t
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hinv : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr hTreal.le
  have hid : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t - W s₀ who =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (A t - W s₀ who) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [ne_of_gt hTreal]
  change |(T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t - W s₀ who| ≤
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, E t
  rw [hid, abs_mul, abs_of_nonneg hinv]
  exact mul_le_mul_of_nonneg_left hsum hinv

/-- Average deviation estimate retaining time-dependent Poisson
corrections. -/
theorem scheduled_deviation_targetAverage_le_initial_of_correction
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : ℕ → G.StationaryMixedProfile)
    (V : ℕ → G.State → Payoff ι) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q c r : ℕ → ℝ)
    (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hclose : ∀ t s, |V t s who - W s who| ≤ q t)
    (hR : ∀ t s, |R t s who| ≤ c t)
    (hstep : ∀ t s (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (x t s) who d)) (fun a =>
          expect (G.transition s a)
            (fun s' => W s' who + R (t + 1) s' who)) ≤
        W s who + R t s who + r t)
    {T : ℕ} (hT : 0 < T) :
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        G.expectedStateValue
          (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
          s₀ t (fun s => V t s who) ≤
      W s₀ who + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q t + c 0 + c t + ∑ k ∈ Finset.range t, r k) := by
  let A : ℕ → ℝ := fun t => G.expectedStateValue
    (Function.update (G.scheduledMarkovBehaviorProfile x) who dev)
    s₀ t (fun s => V t s who)
  let E : ℕ → ℝ := fun t =>
    q t + c 0 + c t + ∑ k ∈ Finset.range t, r k
  have hpoint : ∀ t, A t ≤ W s₀ who + E t := by
    intro t
    dsimp only [A, E]
    simpa only [add_assoc] using
      G.scheduled_deviation_expectedTarget_le_initial_of_correction
        x V W R q c r who dev s₀ hclose hR hstep t
  have hsum : (∑ t ∈ Finset.range T, A t) ≤
      ∑ t ∈ Finset.range T, (W s₀ who + E t) :=
    Finset.sum_le_sum fun t _ => hpoint t
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hinv : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr hTreal.le
  have hmul := mul_le_mul_of_nonneg_left hsum hinv
  change (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t ≤
    W s₀ who + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, E t
  calc
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A t ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (W s₀ who + E t) := hmul
    _ = W s₀ who + (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, E t := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hTreal]

/-- Corrected-potential schedule criterion for a uniform equilibrium payoff.
This is the cancellation-aware replacement for the scalar harmonic-drift
criterion: Poisson corrections are paid through their endpoint bounds. -/
theorem isUniformEquilibriumPayoff_of_scheduledFink_correctedTarget
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (W : G.State → Payoff ι)
    (hcert : ∀ η : ℝ, 0 < η →
      ∃ (β : ℕ → ℝ) (x : ℕ → G.StationaryMixedProfile)
        (V R : ℕ → G.State → Payoff ι)
        (e B q c r : ℕ → ℝ) (T₀ : ℕ),
        G.IsDiscountedStationaryBellmanSchedule β x V ∧
          (∀ t, β t < 1) ∧ G.IsScheduledFinkSwitchBound β V e ∧
          (∀ t s who, |G.scheduledFinkBias β V t s who| ≤ B t) ∧
          (∀ t s who, |V t s who - W s who| ≤ q t) ∧
          (∀ t s who, |R t s who| ≤ c t) ∧
          (∀ t s who,
            |expect (pmfPi (x t s)) (fun a =>
                expect (G.transition s a)
                  (fun s' => W s' who + R (t + 1) s' who)) -
              (W s who + R t s who)| ≤ r t) ∧
          (∀ t s who (d : PMF (G.Act who)),
            expect (pmfPi (Function.update (x t s) who d)) (fun a =>
                expect (G.transition s a)
                  (fun s' => W s' who + R (t + 1) s' who)) ≤
              W s who + R t s who + r t) ∧
          ∀ T, T₀ ≤ T → 0 < T ∧
            ((B 0 + B T) / (T : ℝ) +
              (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, e t ≤ η) ∧
            (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
              (q t + c 0 + c t +
                ∑ k ∈ Finset.range t, r k) ≤ η) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_targetAverages s₀ (W s₀)
  intro η hη
  obtain ⟨β, x, V, R, e, B, q, c, r, T₀,
      hF, hβ1, hswitch, hbias, hclose, hR,
      hharmonic, hexcessive, hasymp⟩ := hcert η hη
  refine ⟨β, x, V, e, B, T₀, hF, hβ1, hswitch, hbias, ?_⟩
  intro T hT
  obtain ⟨hTpos, hboundary, htarget⟩ := hasymp T hT
  refine ⟨hTpos, hboundary, ?_, ?_⟩
  · intro who
    exact (G.scheduled_targetAverage_close_initial_of_correction
      x V W R q c r who s₀ (fun t s => hclose t s who)
      (fun t s => hR t s who) (fun t s => hharmonic t s who) hTpos).trans
        htarget
  · intro who dev
    have hdev := G.scheduled_deviation_targetAverage_le_initial_of_correction
      x V W R q c r who dev s₀ (fun t s => hclose t s who)
        (fun t s => hR t s who)
        (fun t s d => hexcessive t s who d) hTpos
    linarith

end StochasticGame
end GameTheory
