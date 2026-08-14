/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Fink.LimitCore

/-!
# Stationary and interior-correction Fink compilers

Continuity at the undiscounted endpoint, stationary average-reward
verification, interior correction certificates, limit certificates, and the
fast canonical fixed-point family.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter
open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- Auxiliary pure payoffs are jointly continuous in the discount factor and
the Fink-domain point. -/
theorem continuous_finkDiscountedAuxPayoff_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (s : G.State) (a : G.JointAct) (who : ι) :
    Continuous (fun q : ℝ × G.finkDomain U =>
      G.discountedAuxPayoff q.1 (G.finkValue q.2) s a who) := by
  unfold discountedAuxPayoff finkValue
  simp_rw [expect_eq_sum]
  fun_prop

/-- Baseline auxiliary expected payoff is jointly continuous in the discount
factor and Fink coordinates. -/
theorem continuous_finkAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (s : G.State) (who : ι) :
    Continuous (fun q : ℝ × G.finkDomain U =>
      G.finkAuxEU q.1 q.2 s who) := by
  unfold finkAuxEU
  refine continuous_finsetSum (s := (Finset.univ : Finset G.JointAct)) ?_
  intro a ha
  have hw : Continuous (fun q : ℝ × G.finkDomain U =>
      ∏ i, q.2.1.1 (s, i) (a i)) := by
    fun_prop
  exact hw.mul (G.continuous_finkDiscountedAuxPayoff_param s a who)

/-- Pure-deviation auxiliary expected payoff is jointly continuous in the
discount factor and Fink coordinates. -/
theorem continuous_finkDeviationAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (s : G.State) (who : ι) (d : G.Act who) :
    Continuous (fun q : ℝ × G.finkDomain U =>
      G.finkDeviationAuxEU q.1 q.2 s who d) := by
  unfold finkDeviationAuxEU
  refine continuous_finsetSum (s := (Finset.univ : Finset G.JointAct)) ?_
  intro a ha
  have hw : Continuous (fun q : ℝ × G.finkDomain U =>
      (((PMF.pure d) (a who)).toReal) *
        (∏ i ∈ (Finset.univ.erase who), q.2.1.1 (s, i) (a i))) := by
    fun_prop
  exact hw.mul (G.continuous_finkDiscountedAuxPayoff_param s a who)

/-- The auxiliary expected payoff tends to its value at every parameter
point.  This pointwise form keeps later filter compositions lightweight. -/
theorem tendsto_finkAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (q : ℝ × G.finkDomain U) (s : G.State) (who : ι) :
    Tendsto (fun p : ℝ × G.finkDomain U =>
      G.finkAuxEU p.1 p.2 s who) (nhds q)
      (nhds (G.finkAuxEU q.1 q.2 s who)) :=
  (G.continuous_finkAuxEU_param (U := U) s who).tendsto q

/-- The pure-deviation auxiliary payoff tends to its value at every
parameter point. -/
theorem tendsto_finkDeviationAuxEU_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (q : ℝ × G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun p : ℝ × G.finkDomain U =>
      G.finkDeviationAuxEU p.1 p.2 s who d) (nhds q)
      (nhds (G.finkDeviationAuxEU q.1 q.2 s who d)) :=
  (G.continuous_finkDeviationAuxEU_param (U := U) s who d).tendsto q

/-- Joint convergence of the discount and domain point transports through
the auxiliary expected payoff. -/
theorem tendsto_finkAuxEU_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {β : ℕ → ℝ} {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    {φ : ℕ → ℕ} (s : G.State) (who : ι)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    Tendsto ((fun p : ℝ × G.finkDomain U =>
      G.finkAuxEU p.1 p.2 s who) ∘
        fun k => (β (φ k), z (φ k))) atTop
      (nhds (G.finkAuxEU 1 zlim s who)) := by
  have hpair : Tendsto (fun k => (β (φ k), z (φ k))) atTop
      (nhds (1, zlim)) := by
    simpa only [Function.comp_def, nhds_prod_eq] using hβlim.prodMk hzlim
  exact (G.tendsto_finkAuxEU_param (1, zlim) s who).comp hpair

/-- Joint convergence of the discount and domain point transports through a
pure-deviation auxiliary payoff. -/
theorem tendsto_finkDeviationAuxEU_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {β : ℕ → ℝ} {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    {φ : ℕ → ℕ} (s : G.State) (who : ι) (d : G.Act who)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    Tendsto ((fun p : ℝ × G.finkDomain U =>
      G.finkDeviationAuxEU p.1 p.2 s who d) ∘
        fun k => (β (φ k), z (φ k))) atTop
      (nhds (G.finkDeviationAuxEU 1 zlim s who d)) := by
  have hpair : Tendsto (fun k => (β (φ k), z (φ k))) atTop
      (nhds (1, zlim)) := by
    simpa only [Function.comp_def, nhds_prod_eq] using hβlim.prodMk hzlim
  exact (G.tendsto_finkDeviationAuxEU_param (1, zlim) s who d).comp hpair

/-- Convergence of Fink-domain points gives coordinatewise convergence of
their decoded value functions, also after passing to a subsequence. -/
theorem tendsto_finkValue_of_comp_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U} {φ : ℕ → ℕ}
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim))
    (s : G.State) (who : ι) :
    Tendsto (fun k => G.finkValue (z (φ k)) s who) atTop
      (nhds (G.finkValue zlim s who)) := by
  have hz' : Tendsto (fun k => z (φ k)) atTop (nhds zlim) := by
    simpa only [Function.comp_def] using hzlim
  exact G.tendsto_finkValue_apply hz' s who

/-- Two real sequences that agree pointwise have the same limit. -/
theorem tendsto_eq_of_forall_eq {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto f atTop (nhds a)) (hg : Tendsto g atTop (nhds b))
    (hfg : ∀ n, f n = g n) : a = b := by
  have hf' : Tendsto f atTop (nhds b) :=
    hg.congr' (Filter.Eventually.of_forall fun n => (hfg n).symm)
  exact tendsto_nhds_unique hf hf'

/-- If the Fink value equation holds along a convergent sequence whose
discounts tend to one, it also holds at the limit with discount one. -/
theorem finkAuxEU_one_eq_finkValue_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (s : G.State) (who : ι)
    (hvalue : ∀ n,
      G.finkAuxEU (β n) (z n) s who = G.finkValue (z n) s who)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    G.finkAuxEU 1 zlim s who = G.finkValue zlim s who := by
  have haux : Tendsto
      ((fun p : ℝ × G.finkDomain U =>
        G.finkAuxEU p.1 p.2 s who) ∘
          fun k => (β (φ k), z (φ k))) atTop
      (nhds (G.finkAuxEU 1 zlim s who)) :=
    G.tendsto_finkAuxEU_of_tendsto s who hβlim hzlim
  have hval : Tendsto (fun k => G.finkValue (z (φ k)) s who) atTop
      (nhds (G.finkValue zlim s who)) :=
    G.tendsto_finkValue_of_comp_tendsto hzlim s who
  exact tendsto_eq_of_forall_eq haux hval fun k => by
    simpa only [Function.comp_apply] using hvalue (φ k)

/-- Pure-deviation optimality is closed under a convergent vanishing-discount
subsequence. -/
theorem finkDeviationAuxEU_one_le_finkAuxEU_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (s : G.State) (who : ι) (d : G.Act who)
    (hdev : ∀ n,
      G.finkDeviationAuxEU (β n) (z n) s who d ≤
        G.finkAuxEU (β n) (z n) s who)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim)) :
    G.finkDeviationAuxEU 1 zlim s who d ≤ G.finkAuxEU 1 zlim s who := by
  have hleft := G.tendsto_finkDeviationAuxEU_of_tendsto
    s who d hβlim hzlim
  have hright := G.tendsto_finkAuxEU_of_tendsto s who hβlim hzlim
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall fun k => by
    simpa only [Function.comp_apply] using hdev (φ k)

/-- At discount one, the Fink value equation says precisely that the value is
harmonic for the transition kernel induced by the stationary profile. -/
theorem finkValue_harmonic_of_finkAuxEU_one_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι)
    (hlimit : G.finkAuxEU 1 z s who = G.finkValue z s who) :
    G.finkValue z s who =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue z s' who)) := by
  rw [G.finkAuxEU_eq_discountedAuxEU, G.discountedAuxEU_eq] at hlimit
  simpa using hlimit.symm

/-- At discount one, a Fink pure-deviation inequality compares only expected
successor values: the current-stage payoff has vanished. -/
theorem pureDeviationContinuation_le_onProfile_of_finkAuxEU_one_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (hdev : G.finkDeviationAuxEU 1 z s who d ≤ G.finkAuxEU 1 z s who) :
    expect (pmfPi (Function.update (G.finkProfile z s) who (PMF.pure d)))
        (fun a => expect (G.transition s a)
          (fun s' => G.finkValue z s' who)) ≤
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue z s' who)) := by
  rw [G.finkDeviationAuxEU_eq_discountedAuxEU,
    G.finkAuxEU_eq_discountedAuxEU,
    G.discountedAuxEU_eq, G.discountedAuxEU_eq] at hdev
  simpa using hdev

/-- Excessiveness against every pure action extends by linearity to every
mixed action of the deviating player. -/
theorem mixedDeviationContinuation_le_of_pure
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι)
    (hpure : ∀ d : G.Act who,
      expect (pmfPi (Function.update (G.finkProfile z s) who (PMF.pure d)))
          (fun a => expect (G.transition s a)
            (fun s' => G.finkValue z s' who)) ≤
        G.finkValue z s who)
    (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (G.finkProfile z s) who dev))
        (fun a => expect (G.transition s a)
          (fun s' => G.finkValue z s' who)) ≤
      G.finkValue z s who := by
  let f : G.JointAct → ℝ := fun a =>
    expect (G.transition s a) (fun s' => G.finkValue z s' who)
  calc
    expect (pmfPi (Function.update (G.finkProfile z s) who dev)) f =
        expect dev (fun d =>
          expect (pmfPi (Function.update (G.finkProfile z s) who (PMF.pure d)))
            f) := by
          rw [pmfPi_update_bind, expect_bind]
    _ ≤ expect dev (fun _ => G.finkValue z s who) := by
      exact expect_mono dev _ _ hpure
    _ = G.finkValue z s who := expect_const dev _

/-- A convergent family of Fink fixed points with discounts tending to one
has a harmonic limiting continuation value under its limiting stationary
profile.  This is the first limiting equation behind the excessive-function
selection step. -/
theorem finkValue_harmonic_of_fixedPoint_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay (z n) = z n)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim))
    (s : G.State) (who : ι) :
    G.finkValue zlim s who =
      expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) := by
  have hvalue : ∀ n,
      G.finkAuxEU (β n) (z n) s who = G.finkValue (z n) s who := by
    intro n
    exact G.finkAuxEU_eq_finkValue_of_finkMap_fixedPoint
      (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) s who
  have hlimit := G.finkAuxEU_one_eq_finkValue_of_tendsto
    β U z zlim φ s who hvalue hβlim hzlim
  exact G.finkValue_harmonic_of_finkAuxEU_one_eq zlim s who hlimit

/-- The limiting Fink value is excessive against every unilateral pure
action, while it is harmonic on the limiting stationary profile. -/
theorem finkValue_excessive_pureDeviation_of_fixedPoint_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay (z n) = z n)
    (hβlim : Tendsto (β ∘ φ) atTop (nhds 1))
    (hzlim : Tendsto (z ∘ φ) atTop (nhds zlim))
    (s : G.State) (who : ι) (d : G.Act who) :
    expect (pmfPi (Function.update (G.finkProfile zlim s) who (PMF.pure d)))
        (fun a => expect (G.transition s a)
          (fun s' => G.finkValue zlim s' who)) ≤
      G.finkValue zlim s who := by
  have hdev : ∀ n,
      G.finkDeviationAuxEU (β n) (z n) s who d ≤
        G.finkAuxEU (β n) (z n) s who := by
    intro n
    exact G.finkDeviationAuxEU_le_finkAuxEU_of_finkMap_fixedPoint
      (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) s who d
  have hdevLimit := G.finkDeviationAuxEU_one_le_finkAuxEU_of_tendsto
    β U z zlim φ s who d hdev hβlim hzlim
  have hcont :=
    G.pureDeviationContinuation_le_onProfile_of_finkAuxEU_one_le
      zlim s who d hdevLimit
  exact hcont.trans_eq
    (G.finkValue_harmonic_of_fixedPoint_tendsto β U hβ0 hβ1 hpay
      z zlim φ hfix hβlim hzlim s who).symm

/-- A stationary average-reward Bellman certificate closes the verification
problem without any annealing calendar.  Harmonicity/excessiveness transports
the state-dependent target `W` through arbitrary horizons, while the bounded
bias `H` contributes only an endpoint term. -/
theorem isUniformEquilibriumPayoff_of_stationaryAverageRewardBias
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile) (W H : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (x s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfile : ∀ s who,
      W s who + H s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => H s' who)))
    (hdeviation : ∀ s who (dev : PMF (G.Act who)),
      G.mixedStageEU s (Function.update (x s) who dev) who +
          expect (pmfPi (Function.update (x s) who dev)) (fun a =>
            expect (G.transition s a) (fun s' => H s' who)) ≤
        W s who + H s who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ (W s₀)
  intro δ hδ
  let xConst : ℕ → G.StationaryMixedProfile := fun _ => x
  let σ := G.scheduledMarkovBehaviorProfile xConst
  let C : ℝ := ‖H‖
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C / δ)
  refine ⟨σ, N + 1, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (Nat.zero_lt_succ N) hT
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hNT : (N : ℝ) ≤ T := by
    exact_mod_cast (Nat.le_trans (Nat.le_succ N) hT)
  have hratio : 2 * C / δ ≤ (T : ℝ) := hN.trans hNT
  have hboundary : 2 * C / (T : ℝ) ≤ δ := by
    rw [div_le_iff₀ hTreal]
    have hδT : 2 * C ≤ δ * (T : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hδ).mp hratio
    nlinarith
  have hHbound : ∀ t s who, |(fun _ : ℕ => H) t s who| ≤ C :=
    fun _ s who => G.abs_finkBiasCoordinate_le_norm H s who
  have htarget : ∀ who,
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          G.expectedStateValue σ s₀ t (fun s => W s who) =
        W s₀ who := by
    intro who
    have hclose := G.scheduled_targetAverage_close_initial
      xConst (fun _ => W) W (fun _ => 0) (fun _ => 0) who s₀
      (fun _ _ => by simp)
      (fun _ s => by rw [← hharmonic s]; simp) hTpos
    have hzero : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        ((fun _ : ℕ => 0) t +
          ∑ k ∈ Finset.range t, (fun _ : ℕ => 0) k) = 0 := by
      simp
    rw [hzero] at hclose
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hclose (abs_nonneg _)))
  constructor
  · intro who
    have hlo := G.finiteAveragePayoff_ge_targetAverage_of_averageReward_bellman_le
      σ s₀ who (fun _ s => W s who) (fun _ s => H s who)
        (fun _ => 0) (C0 := C) (CT := C)
        (hHbound 0 · who) (hHbound T · who) (fun t h => by
          change W h.2 who + H h.2 who ≤
            G.mixedStageEU h.2 (x h.2) who +
              expect (pmfPi (x h.2)) (fun a =>
                expect (G.transition h.2 a) (fun s' => H s' who)) + 0
          linarith [honProfile h.2 who]) hTpos
    have hup := G.finiteAveragePayoff_le_targetAverage_of_averageReward_bellman_ge
      σ s₀ who (fun _ s => W s who) (fun _ s => H s who)
        (fun _ => 0) (C0 := C) (CT := C)
        (hHbound 0 · who) (hHbound T · who) (fun t h => by
          change G.mixedStageEU h.2 (x h.2) who +
                expect (pmfPi (x h.2)) (fun a =>
                  expect (G.transition h.2 a) (fun s' => H s' who)) ≤
              W h.2 who + H h.2 who + 0
          linarith [honProfile h.2 who]) hTpos
    rw [htarget who] at hlo hup
    simp only [add_zero, Finset.sum_const_zero, mul_zero] at hlo hup
    have hboundary' : (C + C) / (T : ℝ) ≤ δ := by
      simpa only [two_mul] using hboundary
    rw [abs_le]
    constructor <;> linarith
  · intro who dev
    have hexcessiveConst : ∀ t s (d : PMF (G.Act who)),
        expect (pmfPi (Function.update (xConst t s) who d)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) ≤
            W s who + (fun _ : ℕ => 0) t := by
      intro t s d
      simpa only [xConst, add_zero] using hexcessive s who d
    have htargetDev := G.scheduled_deviation_targetAverage_le_initial
      xConst (fun _ => W) W (fun _ => 0) (fun _ => 0) who dev s₀
      (fun _ _ => by simp)
      hexcessiveConst hTpos
    have hup := G.finiteAveragePayoff_le_targetAverage_of_averageReward_bellman_ge
      (Function.update σ who dev) s₀ who
        (fun _ s => W s who) (fun _ s => H s who) (fun _ => 0)
        (C0 := C) (CT := C) (hHbound 0 · who) (hHbound T · who)
        (fun t h => by
          unfold stageEUAt
          rw [G.stageActionDist_update_scheduledMarkovBehaviorProfile]
          dsimp only [xConst]
          change G.mixedStageEU h.2
                (Function.update (x h.2) who (dev t h)) who +
              expect (pmfPi (Function.update (x h.2) who (dev t h)))
                (fun a => expect (G.transition h.2 a)
                  (fun s' => H s' who)) ≤ W h.2 who + H h.2 who + 0
          linarith [hdeviation h.2 who (dev t h)]) hTpos
    simp only [Finset.sum_const_zero, add_zero, mul_zero] at htargetDev hup
    have hboundary' : (C + C) / (T : ℝ) ≤ δ := by
      simpa only [two_mul] using hboundary
    linarith

/-- It is enough to verify the average-reward bias inequality on pure actions
that preserve the harmonic target `W`.  By finiteness, all remaining actions
decrease `W` by one common positive gap.  Adding a sufficiently large multiple
of `W` to the bias leaves the on-profile Bellman equation unchanged and makes
the deviation inequality automatic on those strict-loss actions. -/
theorem isUniformEquilibriumPayoff_of_stationaryAverageRewardBias_on_neutral
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State)
    (x : G.StationaryMixedProfile) (W H : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (honProfile : ∀ s who,
      W s who + H s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => H s' who)))
    (hneutral : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) = W s who →
        G.mixedStageEU s
              (Function.update (x s) who (PMF.pure d)) who +
            expect (pmfPi (Function.update (x s) who (PMF.pure d)))
              (fun a => expect (G.transition s a) (fun s' => H s' who)) ≤
          W s who + H s who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  let D := Σ p : G.State × ι, G.Act p.2
  let base : D → ℝ := fun q =>
    G.mixedStageEU q.1.1
          (Function.update (x q.1.1) q.1.2 (PMF.pure q.2)) q.1.2 +
      expect (pmfPi (Function.update (x q.1.1) q.1.2 (PMF.pure q.2)))
        (fun a => expect (G.transition q.1.1 a) (fun s' => H s' q.1.2)) -
      (W q.1.1 q.1.2 + H q.1.1 q.1.2)
  obtain ⟨B, hB⟩ := Math.Probability.exists_abs_bound_of_finite base
  obtain ⟨δ, hδ, hgap⟩ := G.exists_uniform_strictContinuationGap x W
  let c : ℝ := (|B| + 1) / δ
  let H' : G.State → Payoff ι := fun s who => H s who + c * W s who
  have hc0 : 0 ≤ c := div_nonneg (by positivity) hδ.le
  have hcδ : c * δ = |B| + 1 := by
    dsimp only [c]
    field_simp
  have hcontAdd : ∀ s (mu : PMF G.JointAct) who,
      expect mu (fun a => expect (G.transition s a) (fun s' => H' s' who)) =
        expect mu (fun a => expect (G.transition s a) (fun s' => H s' who)) +
          c * expect mu (fun a =>
            expect (G.transition s a) (fun s' => W s' who)) := by
    intro s mu who
    dsimp only [H']
    simp_rw [expect_add, expect_const_mul]
  have hpure : ∀ s who (d : G.Act who),
      G.mixedStageEU s
            (Function.update (x s) who (PMF.pure d)) who +
          expect (pmfPi (Function.update (x s) who (PMF.pure d)))
            (fun a => expect (G.transition s a) (fun s' => H' s' who)) ≤
        W s who + H' s who := by
    intro s who d
    let contW := expect
      (pmfPi (Function.update (x s) who (PMF.pure d)))
      (fun a => expect (G.transition s a) (fun s' => W s' who))
    rw [hcontAdd]
    change G.mixedStageEU s
          (Function.update (x s) who (PMF.pure d)) who +
        (expect (pmfPi (Function.update (x s) who (PMF.pure d)))
            (fun a => expect (G.transition s a) (fun s' => H s' who)) +
          c * contW) ≤ W s who + (H s who + c * W s who)
    by_cases hstrict : contW < W s who
    · have hgap' := hgap s who d hstrict
      have hbaseUpper : base ⟨(s, who), d⟩ ≤ |B| :=
        (le_abs_self _).trans ((hB ⟨(s, who), d⟩).trans (le_abs_self B))
      have hcLoss : c * (contW - W s who) ≤ c * (-δ) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        dsimp only [contW] at hgap' ⊢
        linarith
      dsimp only [base] at hbaseUpper
      linarith
    · have heq : contW = W s who := by
        apply le_antisymm
        · exact hexcessive s who d
        · exact le_of_not_gt hstrict
      have hn := hneutral s who d (by simpa only [contW] using heq)
      rw [heq]
      linarith
  have hmixedExcessive : ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (x s) who dev)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who := by
    intro s who dev
    exact G.mixedDeviationContinuation_le_of_pure_bound
      x W s who (W s who) (hexcessive s who) dev
  have honProfile' : ∀ s who,
      W s who + H' s who = G.mixedStageEU s (x s) who +
        expect (pmfPi (x s)) (fun a =>
          expect (G.transition s a) (fun s' => H' s' who)) := by
    intro s who
    rw [hcontAdd]
    rw [← hharmonic s who]
    dsimp only [H']
    linarith [honProfile s who]
  have hmixed : ∀ s who (dev : PMF (G.Act who)),
      G.mixedStageEU s (Function.update (x s) who dev) who +
          expect (pmfPi (Function.update (x s) who dev)) (fun a =>
            expect (G.transition s a) (fun s' => H' s' who)) ≤
        W s who + H' s who := by
    intro s who dev
    calc
      G.mixedStageEU s (Function.update (x s) who dev) who +
            expect (pmfPi (Function.update (x s) who dev)) (fun a =>
              expect (G.transition s a) (fun s' => H' s' who)) =
          expect dev (fun d =>
            G.mixedStageEU s
                  (Function.update (x s) who (PMF.pure d)) who +
              expect (pmfPi (Function.update (x s) who (PMF.pure d)))
                (fun a => expect (G.transition s a)
                  (fun s' => H' s' who))) := by
            unfold mixedStageEU
            rw [pmfPi_update_bind]
            rw [expect_bind, expect_bind, expect_add]
      _ ≤ expect dev (fun _ => W s who + H' s who) :=
        expect_mono dev _ _ (hpure s who)
      _ = W s who + H' s who := expect_const dev _
  exact G.isUniformEquilibriumPayoff_of_stationaryAverageRewardBias
    s₀ x W H' hharmonic hmixedExcessive honProfile' hmixed

/-- A finite relative-bias branch closes to a stationary uniform equilibrium
when its singular target-continuation terms are controlled by one further
potential `K`.  The on-profile forcing must converge to the residual of `K`,
while continuation-neutral pure deviations only need the corresponding
asymptotic lower bound.  Strict continuation losses are handled by the finite
gap argument in
`isUniformEquilibriumPayoff_of_stationaryAverageRewardBias_on_neutral`.
Subtracting `K` from the limiting relative bias then gives an average-reward
verification certificate.  This is the finite-bias analogue of one Poisson
correction, and needs no calendar. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hscaledResidual : Tendsto (fun n =>
      (β n / (1 - β n)) • G.finkContinuationResidualVector W (z n))
        atTop (nhds (-G.finkContinuationResidualVector K zlim)))
    (hscaledGainLower : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, -G.finkContinuationGain K zlim s who d - ε ≤
          (β n / (1 - β n)) *
            G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkRelativeBias (β n) W (z n)
  let E : ℕ → G.State → Payoff ι := fun n =>
    G.finkContinuationResidualVector W (z n)
  have hbellman : ∀ n s who,
      G.finkValue (z n) s who + J n s who =
        G.finkStageEU (z n) s who +
          G.finkContinuationEU (J n) (z n) s who +
            a n * E n s who := by
    intro n s who
    simpa only [J, E, a, finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  have hforcing := G.tendsto_smul_finkBellmanForcingVector hz hV
    (by simpa only [J] using hH) a hbellman
  have hforcingCorrection : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim := by
    apply tendsto_nhds_unique hforcing
    simpa only [a, E] using hscaledResidual
  have honProfile : ∀ s who,
      W s who + (H - K) s who =
        G.mixedStageEU s (G.finkProfile zlim s) who +
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a) (fun s' => (H - K) s' who)) := by
    intro s who
    have hcoord := congrFun (congrFun hforcingCorrection s) who
    unfold finkBellmanForcingVector finkContinuationResidualVector
      finkContinuationResidual at hcoord
    change W s who + H s who - G.finkStageEU zlim s who -
        G.finkContinuationEU H zlim s who =
      -(G.finkContinuationEU K zlim s who - K s who) at hcoord
    change W s who + (H - K) s who =
      G.finkStageEU zlim s who +
        G.finkContinuationEU (H - K) zlim s who
    rw [G.finkContinuationEU_sub]
    simp only [Pi.sub_apply] at hcoord ⊢
    linarith
  have hpure : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      G.mixedStageEU s
            (Function.update (G.finkProfile zlim s) who (PMF.pure d)) who +
          expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
              expect (G.transition s a) (fun s' => (H - K) s' who)) ≤
        W s who + (H - K) s who := by
    intro s who d hneutral
    have hstage := G.tendsto_finkStageGain hz s who d
    have hbias := G.tendsto_finkContinuationGain_of_tendsto hH hz s who d
    have hbase : Tendsto (fun n =>
        G.finkStageGain (z n) s who d +
          G.finkContinuationGain
            (G.finkRelativeBias (β n) W (z n)) (z n) s who d)
        atTop (nhds (G.finkStageGain zlim s who d +
          G.finkContinuationGain H zlim s who d)) := by
      exact hstage.add hbias
    have hnonpos : G.finkStageGain zlim s who d +
        G.finkContinuationGain (H - K) zlim s who d ≤ 0 := by
      have hlimit : G.finkStageGain zlim s who d +
          (-G.finkContinuationGain K zlim s who d) +
            G.finkContinuationGain H zlim s who d ≤ 0 := by
        by_contra hnot
        have hpos : 0 < G.finkStageGain zlim s who d +
            (-G.finkContinuationGain K zlim s who d) +
              G.finkContinuationGain H zlim s who d :=
          lt_of_not_ge hnot
        let ε := (G.finkStageGain zlim s who d +
          (-G.finkContinuationGain K zlim s who d) +
            G.finkContinuationGain H zlim s who d) / 4
        have hε : 0 < ε := by
          dsimp only [ε]
          linarith
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbase ε hε
        have hbaseClose : ∀ᶠ n in atTop,
            |(G.finkStageGain (z n) s who d +
                G.finkContinuationGain
                  (G.finkRelativeBias (β n) W (z n)) (z n) s who d) -
              (G.finkStageGain zlim s who d +
                G.finkContinuationGain H zlim s who d)| < ε := by
          filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
          simpa only [Real.dist_eq] using hn
        have hlower := hscaledGainLower s who d hneutral ε hε
        obtain ⟨n, hnclose, hnlower⟩ := (hbaseClose.and hlower).exists
        have hcenter :=
          G.finkCenteredGain_nonpos_of_finkMap_fixedPoint
            (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who d
        rw [abs_lt] at hnclose
        dsimp only [ε] at hnclose hnlower
        linarith
      rw [G.finkContinuationGain_sub]
      linarith
    unfold finkStageGain finkContinuationGain at hnonpos
    have hon := honProfile s who
    linarith
  exact G.isUniformEquilibriumPayoff_of_stationaryAverageRewardBias_on_neutral
    s₀ (G.finkProfile zlim) W (H - K) hharmonic hexcessive
      honProfile hpure

/-- Two-sided convergence is a convenient sufficient condition for the
one-sided pure-deviation control in
`isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate`. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorCorrectionCertificate
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hscaledResidual : Tendsto (fun n =>
      (β n / (1 - β n)) • G.finkContinuationResidualVector W (z n))
        atTop (nhds (-G.finkContinuationResidualVector K zlim)))
    (hscaledGain : ∀ s who (d : G.Act who),
      Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop
          (nhds (-G.finkContinuationGain K zlim s who d))) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H K hfix hz hV hH
      hharmonic hexcessive hscaledResidual
  intro s who d _ ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hscaledGain s who d) ε hε
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  linarith

/-- Algebraic Poisson form of the one-sided interior correction criterion.
The on-profile scaled residual convergence is automatic from the centered
Fink Bellman equation; it is enough to identify its forced limit as the
negative continuation residual of `K`. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonLowerCorrection
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hscaledGainLower : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, -G.finkContinuationGain K zlim s who d - ε ≤
          (β n / (1 - β n)) *
            G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  let a : ℕ → ℝ := fun n => β n / (1 - β n)
  let E : ℕ → G.State → Payoff ι := fun n =>
    G.finkContinuationResidualVector W (z n)
  let J : ℕ → G.State → Payoff ι := fun n =>
    G.finkRelativeBias (β n) W (z n)
  have hbellman : ∀ n s who,
      G.finkValue (z n) s who + J n s who =
        G.finkStageEU (z n) s who +
          G.finkContinuationEU (J n) (z n) s who +
            a n * E n s who := by
    intro n s who
    simpa only [J, E, a, finkContinuationResidualVector] using
      G.finkValue_add_relativeBias_eq_finkEU_add
        (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who
  have hscaledResidual := G.tendsto_smul_finkBellmanForcingVector hz hV
    (by simpa only [J] using hH) a hbellman
  apply G.isUniformEquilibriumPayoff_of_finkInteriorLowerCorrectionCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H K hfix hz hV hH
      hharmonic hexcessive
  · simpa only [a, E, hPoisson] using hscaledResidual
  · exact hscaledGainLower

/-- Harmonic-adjustment form of the interior criterion.  A Poisson solution
may be shifted by any potential harmonic for the limiting on-profile kernel;
the remaining task is precisely to choose that shift so the
continuation-neutral deviation lower bounds hold. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonHarmonicAdjustment
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K A : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hAharmonic : G.finkContinuationResidualVector A zlim = 0)
    (hscaledGainLower : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          -G.finkContinuationGain (K + A) zlim s who d - ε ≤
            (β n / (1 - β n)) *
              G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  have hresidual : G.finkContinuationResidualVector (K + A) zlim =
      G.finkContinuationResidualVector K zlim := by
    rw [G.finkContinuationResidualVector_add, hAharmonic, add_zero]
  apply G.isUniformEquilibriumPayoff_of_finkInteriorPoissonLowerCorrection
    s₀ β U hβ0 hβ1 hpay z zlim W H (K + A) hfix hz hV hH
      hharmonic hexcessive
  · rw [hresidual]
    exact hPoisson
  · exact hscaledGainLower

/-- Support/off-support form of the harmonic-adjustment criterion.  On an
action retained by the limiting profile, the centered Fink equality gives a
finite singular-gain limit, so a static average-reward inequality suffices.
Only continuation-neutral actions that vanish from the limiting support need
an asymptotic lower bound. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonHarmonicAdjustment_onSupport
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K A : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hAharmonic : G.finkContinuationResidualVector A zlim = 0)
    (hsupport : ∀ s who (d : G.Act who),
      G.finkProfile zlim s who d ≠ 0 →
      G.finkStageGain zlim s who d +
        G.finkContinuationGain (H - (K + A)) zlim s who d ≤ 0)
    (hoffSupport : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) = W s who →
      G.finkProfile zlim s who d = 0 →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          -G.finkContinuationGain (K + A) zlim s who d - ε ≤
            (β n / (1 - β n)) *
              G.finkContinuationGain W (z n) s who d) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorPoissonHarmonicAdjustment
    s₀ β U hβ0 hβ1 hpay z zlim W H K A hfix hz hV hH
      hharmonic hexcessive hPoisson hAharmonic
  intro s who d hneutral ε hε
  by_cases hzero : G.finkProfile zlim s who d = 0
  · exact hoffSupport s who d hneutral hzero ε hε
  · have hlimit := G.tendsto_scaled_finkContinuationGain_of_limit_support
      hβ0 hβ1 hpay hz hfix W H hH s who d hzero
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlimit ε hε
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    have hstatic := hsupport s who d hzero
    rw [G.finkContinuationGain_sub] at hstatic
    linarith

/-- Two-sided pure-deviation convergence specializes the one-sided algebraic
Poisson correction criterion. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorPoissonCorrection
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H K : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hPoisson : G.finkBellmanForcingVector W H zlim =
      -G.finkContinuationResidualVector K zlim)
    (hscaledGain : ∀ s who (d : G.Act who),
      Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop
          (nhds (-G.finkContinuationGain K zlim s who d))) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorPoissonLowerCorrection
    s₀ β U hβ0 hβ1 hpay z zlim W H K hfix hz hV hH
      hharmonic hexcessive hPoisson
  intro s who d _ ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hscaledGain s who d) ε hε
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  rw [Real.dist_eq, abs_lt] at hn
  linarith

/-- Zero-correction specialization of
`isUniformEquilibriumPayoff_of_finkInteriorCorrectionCertificate`. -/
theorem isUniformEquilibriumPayoff_of_finkInteriorCertificate
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hscaledResidual : Tendsto (fun n =>
      (β n / (1 - β n)) • G.finkContinuationResidualVector W (z n))
        atTop (nhds 0))
    (hscaledGain : ∀ s who (d : G.Act who),
      Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop (nhds 0)) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorCorrectionCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H 0 hfix hz hV hH
      hharmonic hexcessive
  · have hzero : -G.finkContinuationResidualVector
        (0 : G.State → Payoff ι) zlim = 0 := by
      ext s who
      simp [finkContinuationResidualVector, finkContinuationResidual,
        finkContinuationEU]
    rw [hzero]
    exact hscaledResidual
  · intro s who d
    simpa only [finkContinuationGain, Pi.zero_apply, expect_const,
      sub_self, neg_zero] using hscaledGain s who d

/-- The finite-relative-bias branch closes outright when the limiting value
is state-constant for each player.  In that case every singular target
residual and every pure target-continuation gain is identically zero, so no
Poisson or tangent correction is needed. -/
theorem isUniformEquilibriumPayoff_of_finkInterior_stateConstantValue
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hconstant : ∀ who s t, W s who = W t who) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInteriorCertificate
    s₀ β U hβ0 hβ1 hpay z zlim W H hfix hz hV hH
  · intro s who
    change W s who = G.finkContinuationEU W zlim s who
    exact (G.finkContinuationEU_eq_of_stateConstant
      W hconstant zlim s who).symm
  · intro s who d
    have hfun : (fun t => W t who) = fun _ => W s who := by
      funext t
      exact (hconstant who s t).symm
    rw [hfun]
    simp
  · simpa only [G.finkContinuationResidualVector_eq_zero_of_stateConstant
      W hconstant, smul_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (0 : G.State → Payoff ι)) atTop (nhds 0))
  · intro s who d
    simpa only [G.finkContinuationGain_eq_zero_of_stateConstant
      W hconstant, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- A strictly positive limiting induced state kernel closes the finite-bias
interior branch.  The finite maximum principle first makes the harmonic value
state-constant, after which the zero-correction theorem applies. -/
theorem isUniformEquilibriumPayoff_of_finkInterior_positiveStateKernel
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (s₀ : G.State)
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
    (W H : G.State → Payoff ι)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hz : Tendsto z atTop (nhds zlim))
    (hV : Tendsto (fun n => G.finkValue (z n)) atTop (nhds W))
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hpositive : ∀ s t, G.finkStateKernel zlim s t ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_finkInterior_stateConstantValue
    s₀ β U hβ0 hβ1 hpay z zlim W H hfix hz hV hH
  exact G.stateConstant_of_finkStateKernel_positive_of_harmonic
    zlim W hpositive hharmonic

/-- Canonical vanishing-discount selection yields a stationary profile and
bounded value function that are harmonic on path and excessive against every
unilateral mixed action. -/
theorem exists_finkLimit_harmonic_excessive
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ zlim : G.finkDomain U,
      (∀ s who,
        G.finkValue zlim s who =
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who))) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile zlim s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who := by
  obtain ⟨z, zlim, φ, hfix, hφ, hzlim, hβlim⟩ :=
    G.exists_convergent_approachOne_finkFixedPoint_subsequence U hU hpay
  refine ⟨zlim, ?_, ?_⟩
  · intro s who
    exact G.finkValue_harmonic_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z zlim φ hfix hβlim hzlim s who
  · intro s who dev
    apply G.mixedDeviationContinuation_le_of_pure zlim s who
    intro d
    exact G.finkValue_excessive_pureDeviation_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z zlim φ hfix hβlim hzlim s who d

/-- The canonical limit certificate additionally plays only continuation-
neutral actions.  Strictly value-decreasing actions are absent from its
support and therefore belong to lower-order transient behavior. -/
theorem exists_finkLimit_harmonic_excessive_neutral
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ zlim : G.finkDomain U,
      (∀ s who,
        G.finkValue zlim s who =
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who))) ∧
      (∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile zlim s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who) ∧
      G.IsContinuationNeutralOnSupport (G.finkProfile zlim)
        (G.finkValue zlim) := by
  obtain ⟨zlim, hharmonic, hexcessive⟩ :=
    G.exists_finkLimit_harmonic_excessive U hU hpay
  refine ⟨zlim, hharmonic, hexcessive, ?_⟩
  apply G.isContinuationNeutralOnSupport_of_harmonic_excessive zlim
    (G.finkValue zlim) hharmonic
  intro s who d
  exact hexcessive s who (PMF.pure d)

/-- Canonical Fink fixed points admit a further vanishing-discount family
whose value and transition residuals have the explicit rate `1 / (n + 1)`.
The theorem deliberately makes no claim about the growth of the corresponding
scaled biases. -/
theorem exists_fast_approachOne_finkFixedPoint_family
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (β : ℕ → ℝ) (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U)
      (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1),
      (∀ n, G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n) ∧
      Tendsto β atTop (nhds 1) ∧
      Tendsto z atTop (nhds zlim) ∧
      (∀ s who,
        G.finkValue zlim s who =
          expect (pmfPi (G.finkProfile zlim s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who))) ∧
      (∀ s who (d : G.Act who),
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) ≤ G.finkValue zlim s who) ∧
      G.IsContinuationNeutralOnSupport (G.finkProfile zlim)
        (G.finkValue zlim) ∧
      (∀ n,
        (∀ s who,
          |G.finkValue (z n) s who - G.finkValue zlim s who| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        (∀ s who,
          |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
              expect (G.transition s a)
                (fun s' => G.finkValue zlim s' who)) -
            G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        (∀ s who (d : G.Act who),
          |expect (pmfPi (Function.update (G.finkProfile (z n) s)
              who (PMF.pure d))) (fun a =>
            expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
          expect (pmfPi (Function.update (G.finkProfile zlim s)
              who (PMF.pure d))) (fun a =>
            expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
              (((n + 1 : ℕ) : ℝ))⁻¹) ∧
        ∀ s who (dev : PMF (G.Act who)),
          expect (pmfPi (Function.update (G.finkProfile (z n) s) who dev))
              (fun a => expect (G.transition s a)
                (fun s' => G.finkValue zlim s' who)) ≤
            G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ n s who (d : G.Act who),
        d ∉ G.strictContinuationActions (G.finkProfile zlim)
            (G.finkValue zlim) s who →
        |expect (pmfPi (Function.update (G.finkProfile (z n) s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) - G.finkValue zlim s who| ≤
              (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) < G.finkValue zlim s who →
        ((G.finkProfile (z n) s who) d).toReal * δ ≤
          2 * (((n + 1 : ℕ) : ℝ))⁻¹ := by
  obtain ⟨z₀, zlim, φ, hfix, hφ, hzlim, hβlim⟩ :=
    G.exists_convergent_approachOne_finkFixedPoint_subsequence U hU hpay
  have hharmonic : ∀ s who,
      G.finkValue zlim s who =
        expect (pmfPi (G.finkProfile zlim s)) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) := by
    intro s who
    exact G.finkValue_harmonic_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z₀ zlim φ hfix hβlim hzlim s who
  have hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who := by
    intro s who d
    exact G.finkValue_excessive_pureDeviation_of_fixedPoint_tendsto
      approachOneDiscount U approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay z₀ zlim φ hfix hβlim hzlim s who d
  obtain ⟨ψ, hψ, happrox⟩ :=
    G.exists_strictMono_finkApproximation_subsequence
      (z := z₀ ∘ φ) hzlim hharmonic hexcessive
  let β : ℕ → ℝ := fun n => approachOneDiscount (φ (ψ n))
  let z : ℕ → G.finkDomain U := fun n => z₀ (φ (ψ n))
  have hβ0 : ∀ n, 0 ≤ β n := fun n => approachOneDiscount_nonneg _
  have hβ1 : ∀ n, β n < 1 := fun n => approachOneDiscount_lt_one _
  have hfixFast : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n := by
    intro n
    simpa [β, z] using hfix (φ (ψ n))
  have hβFast : Tendsto β atTop (nhds 1) := by
    have ht := hβlim.comp hψ.tendsto_atTop
    simpa only [β, Function.comp_def] using ht
  have hzFast : Tendsto z atTop (nhds zlim) := by
    have ht := hzlim.comp hψ.tendsto_atTop
    simpa only [z, Function.comp_def] using ht
  have hneutral : G.IsContinuationNeutralOnSupport (G.finkProfile zlim)
      (G.finkValue zlim) := by
    exact G.isContinuationNeutralOnSupport_of_harmonic_excessive
      zlim (G.finkValue zlim) hharmonic hexcessive
  have happroxFast : ∀ n,
      (∀ s who,
        |G.finkValue (z n) s who - G.finkValue zlim s who| ≤
          (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who,
        |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
            expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) -
          G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who (d : G.Act who),
        |expect (pmfPi (Function.update (G.finkProfile (z n) s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile (z n) s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro n
    simpa only [z, Function.comp_apply] using happrox n
  have hprune := G.eventually_all_strictDeviation_probability_mul_le
    hzFast (G.finkValue zlim) (fun n => (((n + 1 : ℕ) : ℝ))⁻¹)
      (fun n => by positivity)
      (fun n s who => by
        have h := (abs_le.mp ((happroxFast n).2.1 s who)).1
        linarith)
      (fun n s who d => (happroxFast n).2.2.2 s who (PMF.pure d))
  have hneutralRate : ∀ n s who (d : G.Act who),
      d ∉ G.strictContinuationActions (G.finkProfile zlim)
          (G.finkValue zlim) s who →
      |expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a)
          (fun s' => G.finkValue zlim s' who)) - G.finkValue zlim s who| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro n s who d hd
    exact G.abs_pureDeviationContinuation_sub_target_le_of_not_mem_strict
      (G.finkProfile zlim) (G.finkProfile (z n)) (G.finkValue zlim)
        s who d (((n + 1 : ℕ) : ℝ))⁻¹ (hexcessive s who d)
          ((happroxFast n).2.2.1 s who d) hd
  exact ⟨β, z, zlim, hβ0, hβ1, hfixFast, hβFast, hzFast,
    hharmonic, hexcessive, hneutral, happroxFast, hneutralRate, hprune⟩

end StochasticGame
end GameTheory
