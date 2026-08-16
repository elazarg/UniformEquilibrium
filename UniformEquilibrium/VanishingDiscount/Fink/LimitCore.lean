/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Fink.Schedule
import MathUE.MeanErgodic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Fink limit and harmonic-support core

Compactness, analytic passage to the vanishing-discount limit,
harmonic-support structure, tangent equations, and quantitative subsequence
selection.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter
open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- The canonical increasing sequence of discount factors approaching one. -/
def approachOneDiscount (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem approachOneDiscount_nonneg (n : ℕ) : 0 ≤ approachOneDiscount n := by
  exact div_nonneg (Nat.cast_nonneg n) (by positivity)

theorem approachOneDiscount_lt_one (n : ℕ) : approachOneDiscount n < 1 := by
  rw [approachOneDiscount, div_lt_one (by positivity)]
  exact_mod_cast Nat.lt_succ_self n

theorem approachOneDiscount_le_one (n : ℕ) : approachOneDiscount n ≤ 1 :=
  (approachOneDiscount_lt_one n).le

theorem tendsto_approachOneDiscount :
    Tendsto approachOneDiscount atTop (nhds 1) := by
  have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hrepr : approachOneDiscount =
      fun n : ℕ => 1 - 1 / ((n : ℝ) + 1) := by
    funext n
    rw [approachOneDiscount]
    field_simp
    ring
  rw [hrepr]
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa using hone.sub hzero

/-- Any bounded family of Fink fixed points indexed by discount factors has
a convergent subsequence in the common compact strategy/value domain. -/
theorem exists_convergent_finkFixedPoint_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ),
      (∀ n, G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay (z n) = z n) ∧
        StrictMono φ ∧ Tendsto (z ∘ φ) atTop (nhds zlim) := by
  have hex : ∀ n, ∃ z : G.finkDomain U,
      G.finkMap (β n) U (hβ0 n) (hβ1 n) hpay z = z :=
    fun n => G.exists_finkMap_fixedPoint (β n) U hU (hβ0 n) (hβ1 n) hpay
  choose z hz using hex
  letI : CompactSpace (G.finkDomain U) :=
    isCompact_iff_compactSpace.mp (G.isCompact_finkDomain U)
  obtain ⟨zlim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq z
  exact ⟨z, zlim, φ, hz, hφ, hlim⟩

/-- Canonical vanishing-discount specialization of compact Fink fixed-point
selection. -/
theorem exists_convergent_approachOne_finkFixedPoint_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (z : ℕ → G.finkDomain U) (zlim : G.finkDomain U) (φ : ℕ → ℕ),
      (∀ n, G.finkMap (approachOneDiscount n) U
          (approachOneDiscount_nonneg n) (approachOneDiscount_le_one n)
          hpay (z n) = z n) ∧
        StrictMono φ ∧ Tendsto (z ∘ φ) atTop (nhds zlim) ∧
          Tendsto (approachOneDiscount ∘ φ) atTop (nhds 1) := by
  obtain ⟨z, zlim, φ, hz, hφ, hlim⟩ :=
    G.exists_convergent_finkFixedPoint_subsequence
      approachOneDiscount U hU approachOneDiscount_nonneg
        approachOneDiscount_le_one hpay
  refine ⟨z, zlim, φ, hz, hφ, hlim, ?_⟩
  exact tendsto_approachOneDiscount.comp hφ.tendsto_atTop

/-- Convergence in Fink's compact domain gives coordinatewise convergence of
the continuation values. -/
theorem tendsto_finkValue_apply
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (s : G.State) (who : ι) :
    Tendsto (fun n => G.finkValue (z n) s who) atTop
      (nhds (G.finkValue zlim s who)) := by
  have hc : Continuous (fun q : G.finkDomain U => q.1.2 s who) := by
    fun_prop
  simpa only [finkValue, Function.comp_def] using (hc.tendsto zlim).comp hz

/-- Convergence in Fink's compact domain gives convergence of the entire
finite-dimensional continuation-value vector. -/
theorem tendsto_finkValue
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) :
    Tendsto (fun n => G.finkValue (z n)) atTop
      (nhds (G.finkValue zlim)) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  exact G.tendsto_finkValue_apply hz s who

/-- The real mixed-action weights converge coordinatewise as well. -/
theorem tendsto_finkStrategyWeight_apply
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (s : G.State) (who : ι)
    (d : G.Act who) :
    Tendsto (fun n => z n |>.1.1 (s, who) d) atTop
      (nhds (zlim.1.1 (s, who) d)) := by
  have hc : Continuous (fun q : G.finkDomain U => q.1.1 (s, who) d) := by
    fun_prop
  exact (hc.tendsto zlim).comp hz

/-- Hence the decoded stationary mixed actions converge pointwise as PMFs. -/
theorem finkProfile_convergesPointwise
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (s : G.State) (who : ι) :
    PMFConvergesPointwise (fun n => G.finkProfile (z n) s who)
      (G.finkProfile zlim s who) := by
  intro d
  have hw := G.tendsto_finkStrategyWeight_apply hz s who d
  have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hw
  change Tendsto (fun n => ENNReal.ofReal (z n |>.1.1 (s, who) d)) atTop
    (nhds (ENNReal.ofReal (zlim.1.1 (s, who) d)))
  simpa only [Function.comp_def] using hof

/-- Against a fixed continuation function, the expected successor value of
the decoded stationary profiles converges along the Fink-domain sequence. -/
theorem tendsto_finkProfile_continuation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → ℝ)
    (s : G.State) :
    Tendsto (fun n => expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
        expect (G.transition s a) W)) atTop
      (nhds (expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) W))) := by
  classical
  have hsum : Tendsto (fun n => ∑ a : G.JointAct,
      ((pmfPi (G.finkProfile (z n) s)) a).toReal *
        expect (G.transition s a) W) atTop
      (nhds (∑ a : G.JointAct,
        ((pmfPi (G.finkProfile zlim s)) a).toReal *
          expect (G.transition s a) W)) := by
    apply tendsto_finsetSum Finset.univ
    intro a ha
    have hw := pmfPi_apply_toReal_tendsto
      (σs := fun n => G.finkProfile (z n) s)
      (σ := G.finkProfile zlim s) a
      (fun i => G.finkProfile_convergesPointwise hz s i (a i))
    exact hw.mul tendsto_const_nhds
  simpa only [expect_eq_sum] using hsum

/-- The same continuation expectation converges after fixing one player's
action to a pure deviation. -/
theorem tendsto_finkProfile_pureDeviationContinuation
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → ℝ)
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n =>
        expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a => expect (G.transition s a) W)) atTop
      (nhds (expect (pmfPi (Function.update (G.finkProfile zlim s)
        who (PMF.pure d))) (fun a => expect (G.transition s a) W))) := by
  have hsum : Tendsto (fun n => ∑ a : G.JointAct,
      ((pmfPi (Function.update (G.finkProfile (z n) s)
        who (PMF.pure d))) a).toReal * expect (G.transition s a) W) atTop
      (nhds (∑ a : G.JointAct,
        ((pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) a).toReal * expect (G.transition s a) W)) := by
    apply tendsto_finsetSum Finset.univ
    intro a ha
    have hmarg : ∀ i, Tendsto (fun n =>
        (Function.update (G.finkProfile (z n) s) who (PMF.pure d)) i (a i))
        atTop (nhds
          ((Function.update (G.finkProfile zlim s) who (PMF.pure d)) i
            (a i))) := by
      intro i
      by_cases hi : i = who
      · subst i
        simp
      · simp only [Function.update_of_ne hi]
        exact G.finkProfile_convergesPointwise hz s i (a i)
    have hw := pmfPi_apply_toReal_tendsto
      (σs := fun n => Function.update (G.finkProfile (z n) s)
        who (PMF.pure d))
      (σ := Function.update (G.finkProfile zlim s) who (PMF.pure d))
      a hmarg
    exact hw.mul tendsto_const_nhds
  simpa only [expect_eq_sum] using hsum

/-- Jointly convergent continuation vectors and Fink-domain points have
convergent continuation gains.  The proof runs through the finite polynomial
coordinate presentation, avoiding any topological claims about `ENNReal`. -/
theorem tendsto_finkContinuationGain_of_tendsto
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {H : ℕ → G.State → Payoff ι} {Hlim : G.State → Payoff ι}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hH : Tendsto H atTop (nhds Hlim)) (hz : Tendsto z atTop (nhds zlim))
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n => G.finkContinuationGain (H n) (z n) s who d) atTop
      (nhds (G.finkContinuationGain Hlim zlim s who d)) := by
  have hpair : Tendsto (fun n => (H n, z n)) atTop (nhds (Hlim, zlim)) := by
    simpa only [nhds_prod_eq] using hH.prodMk hz
  have ht :=
    ((G.continuous_finkContinuationCoordGain_param (U := U) s who d).tendsto
      (Hlim, zlim)).comp hpair
  simpa only [Function.comp_def, G.finkContinuationCoordGain_eq] using ht

/-- One-stage gains converge along a convergent Fink-domain sequence. -/
theorem tendsto_finkStageGain
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (s : G.State) (who : ι) (d : G.Act who) :
    Tendsto (fun n => G.finkStageGain (z n) s who d) atTop
      (nhds (G.finkStageGain zlim s who d)) := by
  have ht := ((G.continuous_finkGain (U := U) 0 s who d).tendsto zlim).comp hz
  simpa only [G.finkGain_zero_eq_finkStageGain, Function.comp_def] using ht

/-- Every state/player coordinate is bounded by the finite-product sup norm. -/
theorem abs_finkBiasCoordinate_le_norm
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    (H : G.State → Payoff ι) (s : G.State) (who : ι) :
    |H s who| ≤ ‖H‖ := by
  have hplayer : ‖H s who‖ ≤ ‖H s‖ := norm_le_pi_norm (H s) who
  have hstate : ‖H s‖ ≤ ‖H‖ := norm_le_pi_norm H s
  simpa only [Real.norm_eq_abs] using hplayer.trans hstate

/-- All on-profile continuation residuals of a target vector. -/
def finkContinuationResidualVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => G.finkContinuationResidual W z s who

/-- A state-constant payoff vector has exactly its current coordinate as
continuation value under every decoded Fink profile. -/
theorem finkContinuationEU_eq_of_stateConstant
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι)
    (hconstant : ∀ who s t, W s who = W t who)
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) :
    G.finkContinuationEU W z s who = W s who := by
  have hfun : (fun t => W t who) = fun _ => W s who := by
    funext t
    exact (hconstant who s t).symm
  unfold finkContinuationEU
  rw [hfun]
  simp

/-- State-constant payoff vectors have zero on-profile continuation
residual, uniformly over the Fink domain. -/
theorem finkContinuationResidualVector_eq_zero_of_stateConstant
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι)
    (hconstant : ∀ who s t, W s who = W t who)
    {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector W z = 0 := by
  ext s who
  unfold finkContinuationResidualVector finkContinuationResidual
  rw [G.finkContinuationEU_eq_of_stateConstant W hconstant]
  simp

/-- State-constant payoff vectors also have zero continuation gain for every
pure deviation, uniformly over the Fink domain. -/
theorem finkContinuationGain_eq_zero_of_stateConstant
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι)
    (hconstant : ∀ who s t, W s who = W t who)
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι)
    (d : G.Act who) :
    G.finkContinuationGain W z s who d = 0 := by
  have hfun : (fun t => W t who) = fun _ => W s who := by
    funext t
    exact (hconstant who s t).symm
  unfold finkContinuationGain
  rw [hfun]
  simp

/-- State transition kernel induced by one decoded stationary Fink profile. -/
def finkStateKernel (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) : PMF G.State :=
  (pmfPi (G.finkProfile z s)).bind (G.transition s)

/-- State transition kernel induced by replacing one player's component of a
decoded stationary Fink profile by a pure action. -/
def finkPureDeviationStateKernel (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) : PMF G.State :=
  (pmfPi (Function.update (G.finkProfile z s)
    who (PMF.pure d))).bind (G.transition s)

/-- Expectations under the induced state kernel are exactly the nested
action/transition expectations used by `finkContinuationEU`. -/
theorem expect_finkStateKernel_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (w : G.State → ℝ) :
    expect (G.finkStateKernel z s) w =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) w) := by
  unfold finkStateKernel
  rw [expect_bind]

/-- Expectations under a pure unilateral-deviation state kernel are exactly
the corresponding nested action/transition expectations. -/
theorem expect_finkPureDeviationStateKernel_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) (w : G.State → ℝ) :
    expect (G.finkPureDeviationStateKernel z s who d) w =
      expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d))) (fun a =>
          expect (G.transition s a) w) := by
  unfold finkPureDeviationStateKernel
  rw [expect_bind]

/-- A Fink continuation gain is the difference between expectations under the
pure-deviation and baseline state kernels. -/
theorem finkContinuationGain_eq_expect_stateKernels
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain W z s who d =
      expect (G.finkPureDeviationStateKernel z s who d) (fun t => W t who) -
        expect (G.finkStateKernel z s) (fun t => W t who) := by
  rw [G.expect_finkPureDeviationStateKernel_eq,
    G.expect_finkStateKernel_eq]
  rfl

/-- If a pure unilateral deviation leaves the state kernel unchanged, then it
has zero continuation gain against every state-payoff vector. -/
theorem finkContinuationGain_eq_zero_of_pureDeviationStateKernel_eq
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (hkernel :
      G.finkPureDeviationStateKernel z s who d =
        G.finkStateKernel z s) :
    G.finkContinuationGain W z s who d = 0 := by
  rw [G.finkContinuationGain_eq_expect_stateKernels, hkernel, sub_self]

/-- Every Fink forcing splits into a harmonic recurrent obstruction and a
Poisson-solvable transient part.  The obstruction is exactly the vector of
Cesàro limits under the induced stationary state kernel. -/
theorem exists_finkHarmonicObstruction_add_continuationResidual
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (F : G.State → Payoff ι) :
    ∃ O K : G.State → Payoff ι,
      G.finkContinuationResidualVector O z = 0 ∧
      F = O + G.finkContinuationResidualVector K z ∧
      ∀ who, Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => F s who)) atTop (nhds (fun s => O s who)) := by
  have hplayer : ∀ who, ∃ o k : G.State → ℝ,
      (∀ s, expect (G.finkStateKernel z s) o = o s) ∧
      (∀ s, F s who = o s +
        (expect (G.finkStateKernel z s) k - k s)) ∧
      Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => F s who)) atTop (nhds o) := by
    intro who
    exact Math.MeanErgodic.exists_harmonic_add_poisson
      (G.finkStateKernel z) (fun s => F s who)
  choose o k ho hdecomp hlim using hplayer
  let O : G.State → Payoff ι := fun s who => o who s
  let K : G.State → Payoff ι := fun s who => k who s
  refine ⟨O, K, ?_, ?_, ?_⟩
  · ext s who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU
    rw [← G.expect_finkStateKernel_eq z s (o who)]
    exact sub_eq_zero.mpr (ho who s)
  · ext s who
    unfold finkContinuationResidualVector finkContinuationResidual
      finkContinuationEU
    change F s who = o who s +
      ((expect (pmfPi (G.finkProfile z s)) fun a =>
        expect (G.transition s a) (k who)) - k who s)
    rw [← G.expect_finkStateKernel_eq z s (k who)]
    exact hdecomp who s
  · intro who
    simpa only [O] using hlim who

/-- Vector forcing represented by an on-profile average-reward Bellman
equation with value `V` and bias `J`. -/
def finkBellmanForcingVector (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (V J : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => V s who + J s who - G.finkStageEU z s who -
    G.finkContinuationEU J z s who

/-- The limiting Bellman forcing has a canonical mean-ergodic split into a
harmonic obstruction and a Poisson-solvable continuation residual. -/
theorem exists_finkBellmanForcing_harmonicObstruction_decomposition
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (W H : G.State → Payoff ι) :
    ∃ O K : G.State → Payoff ι,
      G.finkContinuationResidualVector O z = 0 ∧
      G.finkBellmanForcingVector W H z =
        O + G.finkContinuationResidualVector K z ∧
      ∀ who, Tendsto (fun T : ℕ =>
        (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
          ((Math.MeanErgodic.markovOperator (G.finkStateKernel z)) ^ t)
            (fun s => G.finkBellmanForcingVector W H z s who))
          atTop (nhds (fun s => O s who)) :=
  G.exists_finkHarmonicObstruction_add_continuationResidual z
    (G.finkBellmanForcingVector W H z)

/-- At an interior bias scale, the rescaled Bellman remainder has a finite
limit determined by the limiting value, bias, and stationary profile. -/
theorem tendsto_smul_finkBellmanForcingVector
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    {V J E : ℕ → G.State → Payoff ι}
    {Vlim Jlim : G.State → Payoff ι}
    (hV : Tendsto V atTop (nhds Vlim))
    (hJ : Tendsto J atTop (nhds Jlim)) (a : ℕ → ℝ)
    (hbellman : ∀ n s who, V n s who + J n s who =
      G.finkStageEU (z n) s who +
        G.finkContinuationEU (J n) (z n) s who +
        a n * E n s who) :
    Tendsto (fun n => a n • E n) atTop
      (nhds (G.finkBellmanForcingVector Vlim Jlim zlim)) := by
  apply tendsto_pi_nhds.2
  intro s
  apply tendsto_pi_nhds.2
  intro who
  have hVcoord : Tendsto (fun n => V n s who) atTop
      (nhds (Vlim s who)) := by
    have hc : Continuous (fun H : G.State → Payoff ι => H s who) := by
      fun_prop
    exact (hc.tendsto Vlim).comp hV
  have hJcoord : Tendsto (fun n => J n s who) atTop
      (nhds (Jlim s who)) := by
    have hc : Continuous (fun H : G.State → Payoff ι => H s who) := by
      fun_prop
    exact (hc.tendsto Jlim).comp hJ
  have hstage :=
    ((G.continuous_finkStageEU (U := U) s who).tendsto zlim).comp hz
  have hpair : Tendsto (fun n => (J n, z n)) atTop
      (nhds (Jlim, zlim)) := by
    simpa only [nhds_prod_eq] using hJ.prodMk hz
  have hcontinuation :=
    ((G.continuous_finkContinuationEU_param (U := U) s who).tendsto
      (Jlim, zlim)).comp hpair
  have hforcing := ((hVcoord.add hJcoord).sub hstage).sub hcontinuation
  have hforcing' : Tendsto (fun n => a n * E n s who) atTop
      (nhds (G.finkBellmanForcingVector Vlim Jlim zlim s who)) := by
    apply hforcing.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp only [Function.comp_apply]
      linarith [hbellman n s who]
  simpa only [Pi.smul_apply, smul_eq_mul] using hforcing'

/-- Continuation residuals respect addition. -/
theorem finkContinuationResidualVector_add
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (R K : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector (R + K) z =
      G.finkContinuationResidualVector R z +
        G.finkContinuationResidualVector K z := by
  ext s who
  simp only [finkContinuationResidualVector, finkContinuationResidual,
    Pi.add_apply]
  rw [G.finkContinuationEU_add]
  ring

/-- Continuation residuals respect scalar multiplication. -/
theorem finkContinuationResidualVector_smul
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (c : ℝ) (R : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector (c • R) z =
      c • G.finkContinuationResidualVector R z := by
  ext s who
  simp only [finkContinuationResidualVector, finkContinuationResidual,
    Pi.smul_apply, smul_eq_mul]
  rw [G.finkContinuationEU_smul]
  ring

/-- Continuation residuals respect negation. -/
theorem finkContinuationResidualVector_neg
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (R : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U) :
    G.finkContinuationResidualVector (-R) z =
      -G.finkContinuationResidualVector R z := by
  have hneg : -R = (-1 : ℝ) • R := by
    ext s who
    simp
  rw [hneg, G.finkContinuationResidualVector_smul]
  simp

/-- A unilateral mixed continuation value is the deviating player's
expectation of the corresponding pure-action continuation values. -/
theorem mixedDeviationContinuation_eq_expect_pure
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (x s) who dev))
        (fun a => expect (G.transition s a) (fun s' => W s' who)) =
      expect dev (fun d =>
        expect (pmfPi (Function.update (x s) who (PMF.pure d)))
          (fun a => expect (G.transition s a) (fun s' => W s' who))) := by
  rw [pmfPi_update_bind, expect_bind]

/-- If a finite-distribution expectation reaches a common pointwise upper
bound, every positive-probability point reaches that bound. -/
theorem eq_of_expect_eq_of_forall_le_of_ne_zero
    {α : Type} [Finite α] (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (hexpect : expect μ f = c) (hle : ∀ a, f a ≤ c)
    {a : α} (ha : μ a ≠ 0) : f a = c := by
  apply le_antisymm (hle a)
  by_contra hnot
  have hlt : f a < c := lt_of_not_ge hnot
  have hstrict := expect_lt_const_of_le_of_exists_lt μ f hle ⟨a, ha, hlt⟩
  linarith

/-- Finite maximum principle for a strictly positive induced Fink state
kernel: every harmonic payoff coordinate is constant across states.  This is
the one-step-positive (hence irreducible) structural closure of the
state-constant interior branch. -/
theorem stateConstant_of_finkStateKernel_positive_of_harmonic
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι)
    (hpositive : ∀ s t, G.finkStateKernel z s t ≠ 0)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who))) :
    ∀ who s t, W s who = W t who := by
  intro who s t
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun r => W r who) ⟨s, Finset.mem_univ s⟩
  have hmean : expect (G.finkStateKernel z m) (fun r => W r who) =
      W m who := by
    rw [G.expect_finkStateKernel_eq]
    exact (hharmonic m who).symm
  have hall (r : G.State) : W r who = W m who :=
    eq_of_expect_eq_of_forall_le_of_ne_zero
      (G.finkStateKernel z m) (fun q => W q who) (W m who)
        hmean (fun q => hm q (Finset.mem_univ q)) (hpositive m r)
  exact (hall s).trans (hall t).symm

/-- Quantitative support pruning for a finite distribution.  If one point is
`δ` below a reference level, every point is at most `r` above it, and the
mean is at most `r` below it, then that point's mass times `δ` is at most
`2r`. -/
theorem pmf_apply_toReal_mul_gap_le_two_error
    {α : Type} [Finite α]
    (μ : PMF α) (f : α → ℝ) (c δ r : ℝ) (hr : 0 ≤ r)
    (hmean : c - r ≤ expect μ f)
    (hupper : ∀ b, f b ≤ c + r) {a : α} (ha : f a ≤ c - δ) :
    (μ a).toReal * δ ≤ 2 * r := by
  classical
  let g : α → ℝ := fun b =>
    c + r - if b = a then δ + r else 0
  have hfg : ∀ b, f b ≤ g b := by
    intro b
    by_cases hba : b = a
    · subst b
      dsimp [g]
      simp only [if_true]
      linarith
    · dsimp [g]
      simp only [if_false, hba, sub_zero]
      exact hupper b
  have hE : expect μ f ≤ expect μ g := expect_mono μ f g hfg
  have hindicator :
      expect μ (fun b => if b = a then δ + r else 0) =
        (μ a).toReal * (δ + r) := by
    letI : Fintype α := Fintype.ofFinite α
    rw [expect_eq_sum]
    simp
  have hg : expect μ g = c + r - (μ a).toReal * (δ + r) := by
    unfold g
    rw [expect_sub, expect_const, hindicator]
  rw [hg] at hE
  have hp0 : 0 ≤ (μ a).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg hp0 hr, hmean.trans hE]

/-- A positive real family indexed by a finite predicate has a uniform
positive lower bound.  The predicate may be empty. -/
theorem exists_pos_le_of_finite
    {α : Type} [Finite α] (P : α → Prop) (f : α → ℝ)
    (hpos : ∀ a, P a → 0 < f a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, P a → δ ≤ f a := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let S : Finset ℝ := (Finset.univ.filter P).image f
  by_cases hS : S.Nonempty
  · let δ := S.min' hS
    have hδmem : δ ∈ S := Finset.min'_mem S hS
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hδmem
    have haP : P a := (Finset.mem_filter.mp ha).2
    refine ⟨δ, ?_, ?_⟩
    · simpa [hfa] using hpos a haP
    · intro b hb
      exact Finset.min'_le S (f b)
        (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩)
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha
    exfalso
    exact hS ⟨f a,
      Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩, rfl⟩⟩

/-- A common upper bound for all pure unilateral continuation deviations is
also an upper bound for every mixed unilateral deviation. -/
theorem mixedDeviationContinuation_le_of_pure_bound
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (x : G.StationaryMixedProfile)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) (c : ℝ)
    (hpure : ∀ d : G.Act who,
      expect (pmfPi (Function.update (x s) who (PMF.pure d)))
          (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤ c)
    (dev : PMF (G.Act who)) :
    expect (pmfPi (Function.update (x s) who dev))
        (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤ c := by
  rw [G.mixedDeviationContinuation_eq_expect_pure x W s who dev]
  calc
    expect dev (fun d =>
        expect (pmfPi (Function.update (x s) who (PMF.pure d)))
          (fun a => expect (G.transition s a) (fun s' => W s' who))) ≤
        expect dev (fun _ => c) := expect_mono dev _ _ hpure
    _ = c := expect_const dev c

/-- A strictly continuation-losing action can receive substantial probability
only when the profile's harmonic/excessive errors are substantial. -/
theorem strictContinuation_probability_mul_gap_le
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) (δ r : ℝ) (hr : 0 ≤ r)
    (hharmonic :
      W s who - r ≤ expect (pmfPi (x s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ d' : G.Act who,
      expect (pmfPi (Function.update (x s) who (PMF.pure d'))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + r)
    (hstrict :
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who - δ) :
    ((x s who) d).toReal * δ ≤ 2 * r := by
  classical
  let f : G.Act who → ℝ := fun d' =>
    expect (pmfPi (Function.update (x s) who (PMF.pure d'))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who))
  have hdecomp := G.mixedDeviationContinuation_eq_expect_pure
    x W s who (x s who)
  simp only [Function.update_eq_self] at hdecomp
  apply pmf_apply_toReal_mul_gap_le_two_error
    (x s who) f (W s who) δ r hr
  · rw [← hdecomp]
    exact hharmonic
  · exact hexcessive
  · exact hstrict

/-- Finiteness upgrades all strict continuation losses of a stationary
profile to one common positive gap, simultaneously over states, players, and
actions. -/
theorem exists_uniform_strictContinuationGap
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) < W s who →
        expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) ≤ W s who - δ := by
  let D := Σ p : G.FinkAgent, G.FinkAction p
  let P : D → Prop := fun q =>
    expect (pmfPi (Function.update (x q.1.1) q.1.2 (PMF.pure q.2))) (fun a =>
      expect (G.transition q.1.1 a) (fun s' => W s' q.1.2)) <
        W q.1.1 q.1.2
  let f : D → ℝ := fun q =>
    W q.1.1 q.1.2 -
      expect (pmfPi (Function.update (x q.1.1) q.1.2 (PMF.pure q.2))) (fun a =>
        expect (G.transition q.1.1 a) (fun s' => W s' q.1.2))
  have hpos : ∀ q, P q → 0 < f q := by
    intro q hq
    dsimp [P, f] at hq ⊢
    linarith
  obtain ⟨δ, hδ, hlower⟩ := exists_pos_le_of_finite P f hpos
  refine ⟨δ, hδ, ?_⟩
  intro s who d hstrict
  have hgap := hlower ⟨(s, who), d⟩ hstrict
  dsimp [f] at hgap
  linarith

/-- Pure actions that strictly lower a player's target continuation value
against a reference stationary profile. -/
def strictContinuationActions
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (xref : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) : Finset (G.Act who) :=
  Finset.univ.filter fun d =>
    expect (pmfPi (Function.update (xref s) who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who)) < W s who

/-- Outside the strict-loss set, excessiveness makes a reference action
exactly continuation-neutral.  Therefore coordinatewise approximation of its
continuation value is approximation to the target itself. -/
theorem abs_pureDeviationContinuation_sub_target_le_of_not_mem_strict
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (xref x : G.StationaryMixedProfile) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) (r : ℝ)
    (hexcessive :
      expect (pmfPi (Function.update (xref s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hclose :
      |expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) -
        expect (pmfPi (Function.update (xref s) who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who))| ≤ r)
    (hneutral : d ∉ G.strictContinuationActions xref W s who) :
    |expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ r := by
  have hnlt : ¬ expect (pmfPi (Function.update (xref s) who (PMF.pure d)))
      (fun a => expect (G.transition s a) (fun s' => W s' who)) < W s who := by
    simpa [strictContinuationActions] using hneutral
  have heq : expect (pmfPi (Function.update (xref s) who (PMF.pure d)))
      (fun a => expect (G.transition s a) (fun s' => W s' who)) = W s who :=
    le_antisymm hexcessive (le_of_not_gt hnlt)
  simpa only [heq] using hclose

/-- Every action used with positive probability by a harmonic/excessive
limit profile is continuation-neutral: it preserves the limiting value
against the other players' limiting mixed actions. -/
theorem finkLimit_support_continuation_eq
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι) (s : G.State) (who : ι) (d : G.Act who)
    (hharmonic : W s who =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ d' : G.Act who,
      expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d'))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    (hpos : G.finkProfile z s who d ≠ 0) :
    expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who)) = W s who := by
  have hdecomp := G.mixedDeviationContinuation_eq_expect_pure
    (G.finkProfile z) W s who (G.finkProfile z s who)
  simp only [Function.update_eq_self] at hdecomp
  have hexpect : expect (G.finkProfile z s who) (fun d' =>
      expect (pmfPi (Function.update (G.finkProfile z s)
        who (PMF.pure d'))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who))) = W s who :=
    hdecomp.symm.trans hharmonic.symm
  exact eq_of_expect_eq_of_forall_le_of_ne_zero
    (G.finkProfile z s who) _ (W s who) hexpect hexcessive hpos

/-- A stationary profile is continuation-neutral on its support for `W` if
every positively played pure action preserves that player's expected next
state value against the other players' mixed actions. -/
def IsContinuationNeutralOnSupport (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι]
    (x : G.StationaryMixedProfile) (W : G.State → Payoff ι) : Prop :=
  ∀ s who (d : G.Act who), x s who d ≠ 0 →
    expect (pmfPi (Function.update (x s) who (PMF.pure d))) (fun a =>
      expect (G.transition s a) (fun s' => W s' who)) = W s who

/-- Harmonicity on path and excessiveness against pure deviations imply
continuation-neutrality on the profile's support. -/
theorem isContinuationNeutralOnSupport_of_harmonic_excessive
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (W : G.State → Payoff ι)
    (hharmonic : ∀ s who, W s who =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who) :
    G.IsContinuationNeutralOnSupport (G.finkProfile z) W := by
  intro s who d hpos
  exact G.finkLimit_support_continuation_eq z W s who d
    (hharmonic s who) (hexcessive s who) hpos

/-- An action in the support of a limiting profile is eventually in the
support of every convergent discounted fixed-point profile.  Consequently
its centered higher-order gain equation holds exactly along the tail. -/
theorem eventually_finkCenteredGain_eq_zero_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W : G.State → Payoff ι) (s : G.State) (who : ι)
    (d : G.Act who) (hpos : G.finkProfile zlim s who d ≠ 0) :
    ∀ᶠ n in atTop,
      G.finkStageGain (z n) s who d +
          (β n / (1 - β n)) * G.finkContinuationGain W (z n) s who d +
            G.finkContinuationGain
              (G.finkRelativeBias (β n) W (z n)) (z n) s who d = 0 := by
  have hlimitPos : 0 < zlim.1.1 (s, who) d := by
    rw [← G.finkProfile_apply_toReal zlim s who d]
    exact ENNReal.toReal_pos hpos (PMF.apply_ne_top _ _)
  have ht := G.tendsto_finkStrategyWeight_apply hz s who d
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht
    (zlim.1.1 (s, who) d) hlimitPos
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  have hnpos : G.finkProfile (z n) s who d ≠ 0 := by
    intro hnzero
    have hweightZero : z n |>.1.1 (s, who) d = 0 := by
      rw [← G.finkProfile_apply_toReal (z n) s who d, hnzero]
      simp
    rw [Real.dist_eq, hweightZero, zero_sub, abs_neg,
      abs_of_pos hlimitPos] at hn
    exact (lt_irrefl _ hn)
  exact G.finkCenteredGain_eq_zero_of_finkMap_fixedPoint_of_ne_zero
    (β n) U (hβ0 n) (hβ1 n) hpay (z n) (hfix n) W s who d hnpos

/-- In the finite relative-bias branch, the apparently singular target
continuation residual has a finite limit on every limiting supported action.
Its limit is forced by the next-order centered gain equation. -/
theorem tendsto_scaled_finkContinuationGain_of_limit_support
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℕ → ℝ} {U : ℝ}
    (hβ0 : ∀ n, 0 ≤ β n) (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (W H : G.State → Payoff ι)
    (hH : Tendsto (fun n => G.finkRelativeBias (β n) W (z n))
      atTop (nhds H))
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos : G.finkProfile zlim s who d ≠ 0) :
    Tendsto (fun n => (β n / (1 - β n)) *
        G.finkContinuationGain W (z n) s who d) atTop
      (nhds (-(G.finkStageGain zlim s who d +
        G.finkContinuationGain H zlim s who d))) := by
  have hstage := G.tendsto_finkStageGain hz s who d
  have hbias := G.tendsto_finkContinuationGain_of_tendsto hH hz s who d
  have hneg := (hstage.add hbias).neg
  apply hneg.congr'
  filter_upwards [G.eventually_finkCenteredGain_eq_zero_of_limit_support
    hβ0 hβ1 hpay hz hfix W s who d hpos] with n hn
  linarith

/-- The finite vector space of pure-action coordinates, indexed by state,
player, and that player's action. -/
abbrev FinkPureActionVector (G : StochasticGame ι) :=
  G.State → ∀ who : ι, G.Act who → ℝ

/-- A single coordinate of the finite pure-action vector. -/
abbrev FinkPureActionIndex (G : StochasticGame ι) :=
  G.State × (Σ who : ι, G.Act who)

/-- Codomain of the finite supported tangent system: its first component is
the on-profile harmonicity equation and its second component records the
supported pure-action continuation equations. -/
abbrev FinkSupportTangentEquationVector (G : StochasticGame ι) :=
  (G.State → Payoff ι) × G.FinkPureActionVector

/-- Linear operator of the finite supported tangent system.  Off-support
action coordinates are masked to zero; the first component forces the
adjustment to be harmonic for the limiting on-profile state kernel. -/
noncomputable def finkSupportTangentOperator
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U) :
    (G.State → Payoff ι) →ₗ[ℝ] G.FinkSupportTangentEquationVector :=
  { toFun := fun A =>
      (G.finkContinuationResidualVector A z, fun s who d =>
        if G.finkProfile z s who d ≠ 0 then
          G.finkContinuationGain A z s who d else 0)
    map_add' := by
      intro A B
      apply Prod.ext
      · exact G.finkContinuationResidualVector_add A B z
      · funext s who d
        change (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain (A + B) z s who d else 0) =
          (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain A z s who d else 0) +
          (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain B z s who d else 0)
        by_cases hd : G.finkProfile z s who d ≠ 0
        · rw [if_pos hd, if_pos hd, if_pos hd]
          exact G.finkContinuationGain_add A B z s who d
        · rw [if_neg hd, if_neg hd, if_neg hd, add_zero]
    map_smul' := by
      intro c A
      apply Prod.ext
      · exact G.finkContinuationResidualVector_smul c A z
      · funext s who d
        change (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain (c • A) z s who d else 0) =
          c * (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain A z s who d else 0)
        by_cases hd : G.finkProfile z s who d ≠ 0
        · rw [if_pos hd, if_pos hd]
          exact G.finkContinuationGain_smul c A z s who d
        · rw [if_neg hd, if_neg hd, mul_zero] }

/-- Right-hand side of the finite supported tangent system. -/
noncomputable def finkSupportTangentTarget
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    G.FinkSupportTangentEquationVector :=
  (0, fun s who d =>
    if G.finkProfile z s who d ≠ 0 then
      G.finkStageGain z s who d +
        G.finkContinuationGain (H - K) z s who d else 0)

/-- Solving the operator equation is exactly choosing a harmonic adjustment
that matches every supported tangent gain. -/
theorem finkSupportTangentOperator_eq_target_iff
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K A : G.State → Payoff ι) :
    G.finkSupportTangentOperator z A =
        G.finkSupportTangentTarget z H K ↔
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d := by
  constructor
  · intro heq
    have hfirst := congrArg Prod.fst heq
    change G.finkContinuationResidualVector A z = 0 at hfirst
    refine ⟨hfirst, ?_⟩
    intro s who d hd
    have hcoord := congrFun (congrFun (congrFun
      (congrArg Prod.snd heq) s) who) d
    change (if G.finkProfile z s who d ≠ 0 then
          G.finkContinuationGain A z s who d else 0) =
        (if G.finkProfile z s who d ≠ 0 then
          G.finkStageGain z s who d +
            G.finkContinuationGain (H - K) z s who d else 0) at hcoord
    rwa [if_pos hd, if_pos hd] at hcoord
  · rintro ⟨hharmonic, htangent⟩
    apply Prod.ext
    · change G.finkContinuationResidualVector A z = 0
      exact hharmonic
    · funext s who d
      by_cases hd : G.finkProfile z s who d ≠ 0
      · change (if G.finkProfile z s who d ≠ 0 then
              G.finkContinuationGain A z s who d else 0) =
            (if G.finkProfile z s who d ≠ 0 then
              G.finkStageGain z s who d +
                G.finkContinuationGain (H - K) z s who d else 0)
        rw [if_pos hd, if_pos hd]
        exact htangent s who d hd
      · change (if G.finkProfile z s who d ≠ 0 then
            G.finkContinuationGain A z s who d else 0) =
          (if G.finkProfile z s who d ≠ 0 then
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d else 0)
        rw [if_neg hd, if_neg hd]

/-- Fredholm/Farkas form of supported tangent feasibility.  A harmonic
adjustment exists exactly when every linear functional annihilating the
tangent operator's range also annihilates the required supported target. -/
theorem exists_finkSupportHarmonicAdjustment_iff_forall_dual
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A z = 0 ∧
        ∀ s who (d : G.Act who), G.finkProfile z s who d ≠ 0 →
          G.finkContinuationGain A z s who d =
            G.finkStageGain z s who d +
              G.finkContinuationGain (H - K) z s who d) ↔
    ∀ ℓ : Module.Dual ℝ G.FinkSupportTangentEquationVector,
      (∀ A : G.State → Payoff ι,
        ℓ (G.finkSupportTangentOperator z A) = 0) →
      ℓ (G.finkSupportTangentTarget z H K) = 0 := by
  constructor
  · rintro ⟨A, hA⟩ ℓ hℓ
    rw [← (G.finkSupportTangentOperator_eq_target_iff z H K A).2 hA]
    exact hℓ A
  · intro hdual
    have hmem : G.finkSupportTangentTarget z H K ∈
        LinearMap.range (G.finkSupportTangentOperator z) := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (LinearMap.range (G.finkSupportTangentOperator z))
          (G.finkSupportTangentTarget z H K)).mp
      intro ℓ hℓ
      apply hdual ℓ
      intro A
      exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ
        (G.finkSupportTangentOperator z A) ⟨A, rfl⟩
    obtain ⟨A, hA⟩ := hmem
    exact ⟨A, (G.finkSupportTangentOperator_eq_target_iff z H K A).1 hA⟩

/-- Uniform finite-action pruning: one positive gap controls every strict
limiting continuation deviation, simultaneously over all states and players. -/
theorem eventually_all_strictDeviation_probability_mul_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hharmonic : ∀ n s who,
      W s who - r n ≤ expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ n s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + r n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who →
      ((G.finkProfile (z n) s who) d).toReal * δ ≤ 2 * r n := by
  obtain ⟨Δ, hΔ, hgap⟩ :=
    G.exists_uniform_strictContinuationGap (G.finkProfile zlim) W
  let δ := Δ / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmargin : ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) < W s who →
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who - δ := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro who
    rw [Filter.eventually_all]
    intro d
    by_cases hstrict : expect (pmfPi (Function.update (G.finkProfile zlim s)
        who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) < W s who
    · have ht := G.tendsto_finkProfile_pureDeviationContinuation hz
        (fun s' => W s' who) s who d
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht δ hδ
      filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
      intro _
      have hlimit := hgap s who d hstrict
      rw [Real.dist_eq, abs_lt] at hn
      dsimp [δ] at hn ⊢
      linarith
    · exact Filter.Eventually.of_forall fun _ h => (hstrict h).elim
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmargin] with n hn
  intro s who d hstrict
  exact G.strictContinuation_probability_mul_gap_le
    (G.finkProfile (z n)) W s who d δ (r n) (hr n)
      (hharmonic n s who) (hexcessive n s who) (hn s who d hstrict)

/-- Harmonicity and pure-action excessiveness of a limiting profile become
uniform approximate drift bounds along every convergent finite-state/action
Fink-domain sequence. -/
theorem eventually_finkProfile_harmonic_excessive_close
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    (hharmonic : ∀ s who,
      W s who = expect (pmfPi (G.finkProfile zlim s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop,
      (∀ s who,
        |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
            expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ η) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile (z n) s) who dev)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + η := by
  have hon : ∀ᶠ n in atTop, ∀ s who,
      |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ η := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro who
    have ht := G.tendsto_finkProfile_continuation hz
      (fun s' => W s' who) s
    rw [← hharmonic s who] at ht
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    simpa only [Real.dist_eq] using (le_of_lt hn)
  have hdev : ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) ≤ W s who + η := by
    rw [Filter.eventually_all]
    intro s
    rw [Filter.eventually_all]
    intro who
    rw [Filter.eventually_all]
    intro d
    have ht := G.tendsto_finkProfile_pureDeviationContinuation hz
      (fun s' => W s' who) s who d
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
    filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    linarith [hexcessive s who d]
  filter_upwards [hon, hdev] with n hn hd
  refine ⟨hn, fun s who dev => ?_⟩
  exact G.mixedDeviationContinuation_le_of_pure_bound
    (G.finkProfile (z n)) W s who (W s who + η) (hd s who) dev

/-- Coordinatewise convergence in the finite Fink value cube is eventually
uniform over states and players. -/
theorem eventually_finkValue_close
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ s who,
      |G.finkValue (z n) s who - G.finkValue zlim s who| ≤ η := by
  rw [Filter.eventually_all]
  intro s
  rw [Filter.eventually_all]
  intro who
  have ht := G.tendsto_finkValue_apply hz s who
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  simpa only [Real.dist_eq] using (le_of_lt hn)

/-- Pure-deviation continuation values converge uniformly over the finite
state-player-action coordinates. -/
theorem eventually_finkPureDeviationContinuation_close
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim)) (W : G.State → Payoff ι)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ s who (d : G.Act who),
      |expect (pmfPi (Function.update (G.finkProfile (z n) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) -
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who))| ≤ η := by
  rw [Filter.eventually_all]
  intro s
  rw [Filter.eventually_all]
  intro who
  rw [Filter.eventually_all]
  intro d
  have ht := G.tendsto_finkProfile_pureDeviationContinuation hz
    (fun s' => W s' who) s who d
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht η hη
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  simpa only [Real.dist_eq] using (le_of_lt hn)

/-- A further subsequence can be chosen so value convergence and all
harmonic/excessive transition residuals are bounded explicitly by
`1 / (n + 1)`.  This leaves scaled-bias growth as the only uncontrolled rate. -/
theorem exists_strictMono_finkApproximation_subsequence
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    {z : ℕ → G.finkDomain U} {zlim : G.finkDomain U}
    (hz : Tendsto z atTop (nhds zlim))
    (hharmonic : ∀ s who,
      G.finkValue zlim s who =
        expect (pmfPi (G.finkProfile zlim s)) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)))
    (hexcessive : ∀ s who (d : G.Act who),
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n,
      (∀ s who,
        |G.finkValue (z (ψ n)) s who - G.finkValue zlim s who| ≤
          (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who,
        |expect (pmfPi (G.finkProfile (z (ψ n)) s)) (fun a =>
            expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
          G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      (∀ s who (d : G.Act who),
        |expect (pmfPi (Function.update (G.finkProfile (z (ψ n)) s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
        expect (pmfPi (Function.update (G.finkProfile zlim s)
            who (PMF.pure d))) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
            (((n + 1 : ℕ) : ℝ))⁻¹) ∧
      ∀ s who (dev : PMF (G.Act who)),
        expect (pmfPi (Function.update (G.finkProfile (z (ψ n)) s) who dev))
            (fun a => expect (G.transition s a)
              (fun s' => G.finkValue zlim s' who)) ≤
          G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹ := by
  let P : ℕ → ℕ → Prop := fun n k =>
    (∀ s who,
      |G.finkValue (z k) s who - G.finkValue zlim s who| ≤
        (((n + 1 : ℕ) : ℝ))⁻¹) ∧
    (∀ s who,
      |expect (pmfPi (G.finkProfile (z k) s)) (fun a =>
          expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
        G.finkValue zlim s who| ≤ (((n + 1 : ℕ) : ℝ))⁻¹) ∧
    (∀ s who (d : G.Act who),
      |expect (pmfPi (Function.update (G.finkProfile (z k) s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who)) -
      expect (pmfPi (Function.update (G.finkProfile zlim s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => G.finkValue zlim s' who))| ≤
          (((n + 1 : ℕ) : ℝ))⁻¹) ∧
    ∀ s who (dev : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile (z k) s) who dev))
          (fun a => expect (G.transition s a)
            (fun s' => G.finkValue zlim s' who)) ≤
        G.finkValue zlim s who + (((n + 1 : ℕ) : ℝ))⁻¹
  have hev : ∀ n, ∀ᶠ k in atTop, P n k := by
    intro n
    have hη : 0 < (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
    have hv := G.eventually_finkValue_close hz hη
    have hd := G.eventually_finkProfile_harmonic_excessive_close hz
      (G.finkValue zlim) hharmonic hexcessive hη
    have hpure := G.eventually_finkPureDeviationContinuation_close hz
      (G.finkValue zlim) hη
    filter_upwards [hv, hd, hpure] with k hk hdk hpk
    exact ⟨hk, hdk.1, hpk, hdk.2⟩
  have hexN : ∀ n, ∃ N, ∀ k, N ≤ k → P n k := by
    intro n
    exact Filter.eventually_atTop.mp (hev n)
  choose N hN using hexN
  let ψ : ℕ → ℕ := fun n => Nat.rec (N 0)
    (fun k previous => max (N (k + 1)) (previous + 1)) n
  have hNle : ∀ n, N n ≤ ψ n := by
    intro n
    induction n with
    | zero => simp [ψ]
    | succ n ih =>
        rw [show ψ (n + 1) = max (N (n + 1)) (ψ n + 1) by simp [ψ]]
        exact le_max_left _ _
  have hstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    rw [show ψ (n + 1) = max (N (n + 1)) (ψ n + 1) by simp [ψ]]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  refine ⟨ψ, strictMono_nat_of_lt_succ hstep, ?_⟩
  intro n
  exact hN n (ψ n) (hNle n)

end StochasticGame
end GameTheory
