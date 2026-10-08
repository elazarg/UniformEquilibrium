import Mathlib.Probability.ProductMeasure
import UniformEquilibrium.ProofView.Concepts.Stochastic.Classes.Absorbing
import UniformEquilibrium.ProofView.Concepts.Stochastic.Core.Probability.InfinitePlayLawTransfer

/-!
# Actual stationary play at an absorbing state

The actual infinite-play measure of stationary play from an absorbing initial
state is the independent product of its initial state-action law. Absorption
is used only on supported histories. A state-dependent Markov profile has the
same law as repetition of its mixed action at that initial state.

This module does not reduce an arbitrary initial state to a first-arrival law,
or identify the original paper's state-dependent action histories with padded
histories. Pathwise payoff and deviation conclusions are separate consumers.
-/

noncomputable section

namespace GameTheory.StochasticGame

open MeasureTheory ProbabilityTheory Kernel

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

end GameTheory.StochasticGame
