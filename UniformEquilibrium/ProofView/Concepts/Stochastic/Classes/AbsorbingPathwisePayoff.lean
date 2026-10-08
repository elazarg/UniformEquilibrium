import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import UniformEquilibrium.ProofView.Concepts.Stochastic.Classes.Absorbing
import UniformEquilibrium.ProofView.Concepts.Stochastic.Core.Probability.InfinitePlayLawTransfer
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Asymptotic.LiminfAverageBridge

/-!
# Actual stationary play at an absorbing state

The actual infinite-play measure of stationary play from an absorbing initial
state is the independent product of its initial state-action law. Absorption
is used only on supported histories. A state-dependent Markov profile has the
same law as repetition of its mixed action at that initial state.

This module does not reduce an arbitrary initial state to a first-arrival law,
or identify the original paper's state-dependent action histories with padded
histories. For finite states and actions, the strong law identifies the actual
pathwise average and expected liminf under prescribed stationary Markov play.
An actual stage best-reply inequality also bounds the expected pathwise
liminf of every unilateral full-history behavioral deviation by the same
signed stage payoff. No convergence of a deviation's pathwise averages is
assumed.
-/

noncomputable section

namespace GameTheory.StochasticGame

open MeasureTheory ProbabilityTheory Kernel
open scoped BigOperators
open Filter Topology

section Laws

variable {ι : Type} (G : StochasticGame ι) [Fintype ι]
  [Countable G.State] [∀ who, Countable (G.Act who)]

/-- Actual stationary play from an absorber is the iid product of its state-action law. -/
theorem infinitePlayMeasure_stationaryBehaviorProfile_eq_infinitePi_of_isAbsorbingState
    {initial : G.State} (hAbs : G.IsAbsorbingState initial)
    (actions : ∀ who, PMF (G.Act who)) :
    G.infinitePlayMeasure (G.stationaryBehaviorProfile actions) initial =
      Measure.infinitePi (fun _ : ℕ =>
        (G.initialPMF (G.stationaryBehaviorProfile actions) initial).toMeasure) := by
  classical
  let profile := G.stationaryBehaviorProfile actions
  let law := (G.initialPMF profile initial).toMeasure
  let independent (time : ℕ) :
      Kernel ((index : Finset.Iic time) → G.StageOutcome) G.StageOutcome :=
    Kernel.const _ law
  let (time : ℕ) : IsMarkovKernel (independent time) := by
    dsimp [independent, law]
    infer_instance
  have hlast : ∀ time, ∀ᵐ historyCoords ∂(G.coordsDist profile initial time).toMeasure,
      (historyCoords ⟨time, Finset.mem_Iic.mpr le_rfl⟩).1 = initial := by
    intro time
    rw [ae_iff]
    apply (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete).mpr
    refine Set.disjoint_left.mpr ?_
    intro historyCoords hprefix hnot
    have hhistory : G.histOfIic time historyCoords ∈ (G.histDist profile initial time).support := by
      rw [← G.map_histOfIic_coordsDist profile initial time, PMF.mem_support_map_iff]
      exact ⟨historyCoords, hprefix, rfl⟩
    exact hnot (G.snd_eq_of_mem_support_histDist_of_isAbsorbingState
      hAbs profile time _ hhistory)
  have hstep : ∀ time (historyCoords : (index : Finset.Iic time) → G.StageOutcome),
      (historyCoords ⟨time, Finset.mem_Iic.mpr le_rfl⟩).1 = initial →
        G.stepKernel profile time historyCoords = independent time historyCoords := by
    intro time historyCoords hstate
    change (G.stepPMF profile time historyCoords).toMeasure = law
    unfold stepPMF
    rw [hstate, hAbs, PMF.pure_bind]
    simp only [profile, G.stageActionDist_stationaryBehaviorProfile]
    rfl
  have hfinite : ∀ time,
      (partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel profile) 0 time) ∘ₘ
        G.startMeasure profile initial =
        (partialTraj (X := fun _ : ℕ => G.StageOutcome) independent 0 time) ∘ₘ
          G.startMeasure profile initial := by
    intro time
    induction time with
    | zero => rw [partialTraj_self, partialTraj_self]
    | succ time ih =>
        rw [partialTraj_succ_eq_comp (Nat.zero_le time),
          partialTraj_succ_eq_comp (Nat.zero_le time),
          ← Measure.comp_assoc, ← Measure.comp_assoc, ← ih]
        apply Measure.comp_congr
        have hpersistence : ∀ᵐ historyCoords ∂
            (partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel profile) 0 time) ∘ₘ
              G.startMeasure profile initial,
            (historyCoords ⟨time, Finset.mem_Iic.mpr le_rfl⟩).1 = initial := by
          change ∀ᵐ historyCoords ∂Measure.bind (G.startMeasure profile initial)
              (partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel profile) 0 time), _
          rw [G.bind_partialTraj_eq_coordsDist_toMeasure]
          exact hlast time
        filter_upwards [hpersistence] with historyCoords hstate
        rw [partialTraj_succ_self, partialTraj_succ_self]
        simp only [Kernel.map_apply _ (measurable_IicProdIoc (X := fun _ : ℕ => G.StageOutcome)),
          Kernel.prod_apply, Kernel.map_apply _
            (MeasurableEquiv.piSingleton (X := fun _ : ℕ => G.StageOutcome) time).measurable]
        rw [hstep time historyCoords hstate]
  have hstart : G.startMeasure profile initial =
      Measure.pi (fun _ : Finset.Iic 0 => law) := by
    change law.map (MeasurableEquiv.piUnique
      (fun _ : Finset.Iic 0 => G.StageOutcome)).symm = _
    exact (MeasurePreserving.symm (MeasurableEquiv.piUnique _)
      (measurePreserving_piUnique (fun _ : Finset.Iic 0 => law))).map_eq
  have hproduct : (traj (X := fun _ : ℕ => G.StageOutcome) independent 0) ∘ₘ
      G.startMeasure profile initial =
      Measure.infinitePi (fun _ : ℕ => law) := by
    rw [hstart]
    change Measure.infinitePiNat (fun _ : ℕ => law) = Measure.infinitePi (fun _ : ℕ => law)
    exact (Measure.isProjectiveLimit_infinitePiNat (fun _ : ℕ => law)).unique
      (Measure.isProjectiveLimit_infinitePi (fun _ : ℕ => law))
  have hmarginals : ∀ time,
      (G.infinitePlayMeasure profile initial).map
          (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) time) =
        (Measure.infinitePi (fun _ : ℕ => law)).map
          (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) time) := by
    intro time
    have hactual : G.infinitePlayMeasure profile initial =
        (traj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel profile) 0) ∘ₘ
          G.startMeasure profile initial := rfl
    rw [hactual, ← hproduct, Measure.map_comp _ _ (by fun_prop),
      Measure.map_comp _ _ (by fun_prop), traj_map_frestrictLe, traj_map_frestrictLe]
    exact hfinite time
  have hprojective : IsProjectiveLimit (G.infinitePlayMeasure profile initial)
      (fun indices : Finset ℕ => Measure.pi (fun _ : indices => law)) := by
    apply (isProjectiveLimit_nat_iff
      (isProjectiveMeasureFamily_pi (fun _ : ℕ => law)) _).mpr
    intro time
    rw [hmarginals time]
    exact Measure.infinitePi_map_restrict (fun _ : ℕ => law)
  exact hprojective.unique (Measure.isProjectiveLimit_infinitePi (fun _ : ℕ => law))

/-- At an absorbing initial state, Markov play uses only that state's stationary action law. -/
theorem infinitePlayMeasure_markovBehaviorProfile_eq_stationary_of_isAbsorbingState
    {initial : G.State} (hAbs : G.IsAbsorbingState initial)
    (actions : G.State → ∀ who, PMF (G.Act who)) :
    G.infinitePlayMeasure (G.markovBehaviorProfile actions) initial =
      G.infinitePlayMeasure (G.stationaryBehaviorProfile (actions initial)) initial := by
  apply G.infinitePlayMeasure_eq_of_stageActionDist_eq_on_support
  intro time history hhistory
  have hstate := G.snd_eq_of_mem_support_histDist_of_isAbsorbingState
    hAbs (G.markovBehaviorProfile actions) time history hhistory
  rw [G.stageActionDist_markovBehaviorProfile, hstate,
    G.stageActionDist_stationaryBehaviorProfile]

/-- From an absorber, Markov and stationary opponents induce the same law for the same deviation. -/
theorem infinitePlayMeasure_update_markovBehaviorProfile_eq_stationary_of_isAbsorbingState
    [DecidableEq ι] {initial : G.State} (hAbs : G.IsAbsorbingState initial)
    (actions : G.State → ∀ who, PMF (G.Act who)) (who : ι)
    (dev : G.BehaviorStrategy who) :
    G.infinitePlayMeasure (Function.update (G.markovBehaviorProfile actions) who dev) initial =
      G.infinitePlayMeasure
        (Function.update (G.stationaryBehaviorProfile (actions initial)) who dev) initial := by
  apply G.infinitePlayMeasure_eq_of_stageActionDist_eq_on_support
  intro time history hhistory
  have hstate := G.snd_eq_of_mem_support_histDist_of_isAbsorbingState hAbs
    (Function.update (G.markovBehaviorProfile actions) who dev) time history hhistory
  rw [G.stageActionDist_update_markovBehaviorProfile, hstate,
    G.stageActionDist_update_stationaryBehaviorProfile]

end Laws

section FinitePayoffs

variable {ι : Type} (G : StochasticGame ι) [Fintype ι]
  [Finite G.State] [∀ who, Finite (G.Act who)]

/-- From an absorber, actual stationary path averages converge to the mixed stage payoff. -/
theorem ae_tendsto_pathwiseAveragePayoff_stationary_of_isAbsorbingState
    {initial : G.State} (hAbs : G.IsAbsorbingState initial)
    (actions : ∀ who, PMF (G.Act who)) (who : ι) :
    ∀ᵐ play ∂G.infinitePlayMeasure (G.stationaryBehaviorProfile actions) initial,
      Tendsto (fun horizon => G.pathwiseAveragePayoff who horizon play) atTop
        (𝓝 (G.mixedStageEU initial actions who)) := by
  classical
  let : Fintype G.State := Fintype.ofFinite G.State
  let : ∀ player, Fintype (G.Act player) := fun player => Fintype.ofFinite (G.Act player)
  let profile := G.stationaryBehaviorProfile actions
  let law : Measure G.StageOutcome := (G.initialPMF profile initial).toMeasure
  let product : Measure G.Play := Measure.infinitePi (fun _ : ℕ => law)
  let observable : G.StageOutcome → ℝ := fun outcome =>
    G.stagePayoff outcome.1 outcome.2 who
  let process : ℕ → G.Play → ℝ := fun time play => observable (play time)
  have hmeas : Measurable observable := Measurable.of_discrete
  have hint : Integrable (process 0) product :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => law) 0).integrable_comp_of_integrable
      (Integrable.of_finite (f := observable))
  have hindep : Pairwise (fun first second => process first ⟂ᵢ[product] process second) := by
    intro first second hne
    exact (iIndepFun_infinitePi (P := fun _ : ℕ => law)
      (X := fun _ : ℕ => observable) (fun _ => hmeas)).indepFun hne
  have hident : ∀ time, IdentDistrib (process time) (process 0) product product := by
    intro time
    have heval : IdentDistrib (fun play : G.Play => play time)
        (fun play : G.Play => play 0) product product := by
      refine ⟨(measurable_pi_apply time).aemeasurable,
        (measurable_pi_apply 0).aemeasurable, ?_⟩
      exact (Measure.infinitePi_map_eval (fun _ : ℕ => law) time).trans
        (Measure.infinitePi_map_eval (fun _ : ℕ => law) 0).symm
    exact heval.comp hmeas
  have hlaw : G.infinitePlayMeasure profile initial = product :=
    G.infinitePlayMeasure_stationaryBehaviorProfile_eq_infinitePi_of_isAbsorbingState
      hAbs actions
  have hmean : ∫ play, process 0 play ∂product = G.mixedStageEU initial actions who := by
    rw [← hlaw]
    have hone : (fun play : G.Play => process 0 play) =
        G.pathwiseAveragePayoff who 1 := by
      funext play
      simp only [process, observable, pathwiseAveragePayoff, totalPayoff, histOfPlay,
        Nat.cast_one, inv_one, one_mul, Fin.sum_univ_one]
      rfl
    rw [hone, G.integral_pathwiseAveragePayoff,
      G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
    simp only [Finset.sum_range_one, Nat.cast_one, inv_one, one_mul]
    exact G.expectedStagePayoff_stationaryBehaviorProfile_of_isAbsorbingState
      hAbs actions 0 who
  have haverage (horizon : ℕ) (play : G.Play) :
      (∑ time ∈ Finset.range horizon, process time play) / (horizon : ℝ) =
        G.pathwiseAveragePayoff who horizon play := by
    change _ = (horizon : ℝ)⁻¹ * ∑ time : Fin horizon, process time.1 play
    rw [Fin.sum_univ_eq_sum_range (fun time => process time play) horizon,
      div_eq_mul_inv, mul_comm]
  have hlimit := strong_law_ae_real process hint hindep hident
  rw [hmean] at hlimit
  simpa only [haverage, ← hlaw, profile] using hlimit

/-- A state-dependent Markov profile has the same actual absorber average as its initial action. -/
theorem ae_tendsto_pathwiseAveragePayoff_markov_of_isAbsorbingState
    {initial : G.State} (hAbs : G.IsAbsorbingState initial)
    (actions : G.State → ∀ who, PMF (G.Act who)) (who : ι) :
    ∀ᵐ play ∂G.infinitePlayMeasure (G.markovBehaviorProfile actions) initial,
      Tendsto (fun horizon => G.pathwiseAveragePayoff who horizon play) atTop
        (𝓝 (G.mixedStageEU initial (actions initial) who)) := by
  rw [G.infinitePlayMeasure_markovBehaviorProfile_eq_stationary_of_isAbsorbingState
    hAbs actions]
  exact G.ae_tendsto_pathwiseAveragePayoff_stationary_of_isAbsorbingState
    hAbs (actions initial) who

/-- Literal expected pathwise liminf equals the signed mixed stage payoff at an absorber. -/
theorem integral_liminf_pathwiseAveragePayoff_markov_of_isAbsorbingState
    {initial : G.State} (hAbs : G.IsAbsorbingState initial)
    (actions : G.State → ∀ who, PMF (G.Act who)) (who : ι) :
    ∫ play, liminf (fun horizon => G.pathwiseAveragePayoff who horizon play) atTop
        ∂G.infinitePlayMeasure (G.markovBehaviorProfile actions) initial =
      G.mixedStageEU initial (actions initial) who := by
  have hlimit := G.ae_tendsto_pathwiseAveragePayoff_markov_of_isAbsorbingState
    hAbs actions who
  calc
    _ = ∫ _play, G.mixedStageEU initial (actions initial) who
        ∂G.infinitePlayMeasure (G.markovBehaviorProfile actions) initial := by
      apply integral_congr_ae
      filter_upwards [hlimit] with play hplay
      exact hplay.liminf_eq
    _ = _ := by simp

/-- Every full-history deviation at an absorber obeys its signed mixed stage best-reply cap. -/
theorem integral_liminf_pathwiseAveragePayoff_update_markov_le_of_isAbsorbingState
    [DecidableEq ι] {initial : G.State} (hAbs : G.IsAbsorbingState initial)
    (actions : G.State → ∀ who, PMF (G.Act who)) (who : ι)
    (hm : ∀ deviation : PMF (G.Act who),
      G.mixedStageEU initial (Function.update (actions initial) who deviation) who ≤
        G.mixedStageEU initial (actions initial) who)
    (dev : G.BehaviorStrategy who) :
    ∫ play, liminf (fun horizon => G.pathwiseAveragePayoff who horizon play) atTop
        ∂G.infinitePlayMeasure (Function.update (G.markovBehaviorProfile actions) who dev)
          initial ≤
      G.mixedStageEU initial (actions initial) who := by
  classical
  let : Fintype G.State := Fintype.ofFinite G.State
  let : ∀ player, Fintype (G.Act player) := fun player => Fintype.ofFinite (G.Act player)
  rw [G.infinitePlayMeasure_update_markovBehaviorProfile_eq_stationary_of_isAbsorbingState
    hAbs actions who dev]
  obtain ⟨bound, hbound⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun outcome : G.StageOutcome => G.stagePayoff outcome.1 outcome.2 who)
  obtain ⟨outcome, _⟩ :=
    (G.initialPMF (G.stationaryBehaviorProfile (actions initial)) initial).support_nonempty
  have hbound0 : 0 ≤ bound := (abs_nonneg _).trans (hbound outcome)
  apply integral_liminf_le_of_bounded_of_eventually_le
    (G.measurable_pathwiseAveragePayoff who)
    (G.abs_pathwiseAveragePayoff_le who hbound0 (fun state action => hbound (state, action)))
  filter_upwards [eventually_gt_atTop 0] with horizon hpositive
  rw [G.integral_pathwiseAveragePayoff]
  exact G.finiteAveragePayoff_le_of_forall_expectedStagePayoff_le_of_pos
    (Function.update (G.stationaryBehaviorProfile (actions initial)) who dev)
    initial who horizon hpositive
    (fun time _ => G.expectedStagePayoff_update_stationaryBehaviorProfile_le_of_isAbsorbingState
      hAbs hm dev time)

end FinitePayoffs

end GameTheory.StochasticGame
