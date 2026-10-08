import UniformEquilibrium.ProofView.Concepts.Stochastic.Classes.Absorbing
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Asymptotic.LiminfAverageBridge
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Actual path averages with action-independent absorbing rewards

Every behavioral profile preserves an absorbing state almost surely once it
has arrived there. If all states other than one distinguished live state are
absorbing and stage rewards are action-independent, actual path averages
converge almost surely. The live reward need not be zero and rewards may be
signed. These facts use countable states and actions, not a supplied path law,
positive absorption probability, or stationary-profile restriction.
-/

noncomputable section

namespace GameTheory.StochasticGame

open Filter MeasureTheory
open scoped BigOperators Topology

variable {ι : Type} (G : StochasticGame ι) [Fintype ι]

/-- A supported one-stage extension cannot leave its absorbing previous state. -/
private theorem supported_history_succ_of_isAbsorbingState
    (σ : G.BehaviorProfile) (initial : G.State) (n : ℕ)
    (history : G.Hist (n + 1))
    (hsupport : history ∈ (G.histDist σ initial (n + 1)).support)
    (hAbs : G.IsAbsorbingState (history.1 (Fin.last n)).1) :
    history.2 = (history.1 (Fin.last n)).1 := by
  obtain ⟨previous, -, action, -, next, hnext, rfl⟩ :=
    (G.mem_support_histDist_succ σ initial n history).mp hsupport
  simp only [Fin.snoc_last] at hAbs
  rw [hAbs action] at hnext
  simpa only [Fin.snoc_last] using (PMF.mem_support_pure_iff _ _).mp hnext

omit [Fintype ι] in
/-- Persistence makes an action-independent single-live-state path average converge. -/
private theorem exists_pathwiseAveragePayoff_limit_of_actionIndependent_singleLive
    (live : G.State)
    (habsorbing : ∀ state, state ≠ live → G.IsAbsorbingState state)
    (who : ι)
    (hpayoff : ∀ state first second,
      G.stagePayoff state first who = G.stagePayoff state second who)
    (play : G.Play)
    (hpersist : ∀ n, G.IsAbsorbingState (play n).1 → (play (n + 1)).1 = (play n).1) :
    ∃ value : ℝ, Tendsto (fun n => G.pathwiseAveragePayoff who n play)
      atTop (𝓝 value) := by
  classical
  let stage : ℕ → ℝ := fun n => G.stagePayoff (play n).1 (play n).2 who
  have haverage : ∀ n, G.pathwiseAveragePayoff who n play =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, stage k := by
    intro n
    change (n : ℝ)⁻¹ * (∑ k : Fin n, stage k.1) = _
    exact congrArg (fun value : ℝ => (n : ℝ)⁻¹ * value)
      (Fin.sum_univ_eq_sum_range stage n)
  by_cases hlive : ∀ n, (play n).1 = live
  · have hstage : stage = fun _ => G.stagePayoff live (play 0).2 who := by
      funext n
      dsimp only [stage]
      rw [hlive n]
      exact hpayoff live (play n).2 (play 0).2
    have hlimit : Tendsto stage atTop (𝓝 (G.stagePayoff live (play 0).2 who)) := by
      rw [hstage]
      exact tendsto_const_nhds
    refine ⟨G.stagePayoff live (play 0).2 who, ?_⟩
    simpa only [haverage] using hlimit.cesaro
  · obtain ⟨time, htime⟩ := not_forall.mp hlive
    have htail : ∀ offset, (play (time + offset)).1 = (play time).1 := by
      intro offset
      induction offset with
      | zero => simp only [Nat.add_zero]
      | succ offset ih =>
          have hAbs : G.IsAbsorbingState (play (time + offset)).1 := by
            rw [ih]
            exact habsorbing (play time).1 htime
          simpa only [Nat.add_succ] using (hpersist (time + offset) hAbs).trans ih
    have hevent : stage =ᶠ[atTop] fun _ =>
        G.stagePayoff (play time).1 (play time).2 who := by
      filter_upwards [eventually_ge_atTop time] with n hn
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hn
      dsimp only [stage]
      rw [htail offset]
      exact hpayoff (play time).1 (play (time + offset)).2 (play time).2
    have hstage : Tendsto stage atTop
        (𝓝 (G.stagePayoff (play time).1 (play time).2 who)) :=
      tendsto_const_nhds.congr' hevent.symm
    refine ⟨G.stagePayoff (play time).1 (play time).2 who, ?_⟩
    simpa only [haverage] using hstage.cesaro

section CountableLaws

variable [Countable G.State] [∀ who, Countable (G.Act who)]

/-- Every actual behavioral play preserves each absorbing state once it is reached. -/
theorem ae_isAbsorbingState_persists (σ : G.BehaviorProfile) (initial : G.State) :
    ∀ᵐ play ∂G.infinitePlayMeasure σ initial,
      ∀ n, G.IsAbsorbingState (play n).1 → (play (n + 1)).1 = (play n).1 := by
  classical
  have hsupport : ∀ n, ∀ᵐ history ∂(G.histDist σ initial n).toMeasure,
      history ∈ (G.histDist σ initial n).support := by
    intro n
    rw [ae_iff]
    apply (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete).2
    exact Set.disjoint_left.mpr fun _ hmem hnot => hnot hmem
  have hplay : ∀ n, ∀ᵐ play ∂G.infinitePlayMeasure σ initial,
      G.histOfPlay n play ∈ (G.histDist σ initial n).support := by
    intro n
    apply ae_of_ae_map (G.measurable_histOfPlay n).aemeasurable
    rw [G.map_histOfPlay_infinitePlayMeasure]
    exact hsupport n
  filter_upwards [ae_all_iff.mpr hplay] with play hplay
  intro n hAbs
  exact supported_history_succ_of_isAbsorbingState G σ initial n
    (G.histOfPlay (n + 1) play) (hplay (n + 1)) hAbs

/-- Action-independent single-live-state games have convergent actual behavioral averages. -/
theorem ae_tendsto_pathwiseAveragePayoff_liminf_of_actionIndependent_singleLive
    (live : G.State)
    (habsorbing : ∀ state, state ≠ live → G.IsAbsorbingState state)
    (who : ι)
    (hpayoff : ∀ state first second,
      G.stagePayoff state first who = G.stagePayoff state second who)
    (σ : G.BehaviorProfile) (initial : G.State) :
    ∀ᵐ play ∂G.infinitePlayMeasure σ initial,
      Tendsto (fun n => G.pathwiseAveragePayoff who n play) atTop
        (𝓝 (liminf (fun n => G.pathwiseAveragePayoff who n play) atTop)) := by
  filter_upwards [G.ae_isAbsorbingState_persists σ initial] with play hpersist
  obtain ⟨value, hvalue⟩ :=
    exists_pathwiseAveragePayoff_limit_of_actionIndependent_singleLive G live
      habsorbing who hpayoff play hpersist
  simpa only [hvalue.liminf_eq] using hvalue

end CountableLaws

end GameTheory.StochasticGame
