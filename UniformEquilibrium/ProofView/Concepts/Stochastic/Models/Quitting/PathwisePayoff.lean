import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.RootContinuation
import UniformEquilibrium.ProofView.Concepts.Stochastic.Classes.ActionIndependentAbsorptionPayoff

/-!
# Actual expected pathwise limiting payoff of quitting games

Every behavioral profile, including every full-history unilateral deviation,
has almost-sure convergence of its actual path averages. At the live initial
state their expected liminf equals the existing terminal payoff; at an absorbed
initial state it equals that state's reward. The live identity uses uniqueness
of limits and the already proved terminal expected-average convergence.
No stationary, Nash, payoff-sign, or positive-absorption premise is imposed.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter MeasureTheory
open scoped Topology

variable {ι : Type} [Fintype ι]

local instance (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Finite (quittingGame reward).State :=
  inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))

local instance (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Finite ((quittingGame reward).Act who) := inferInstanceAs (Finite Bool)

/-- All actual quitting-game behavioral profiles have convergent path averages. -/
theorem ae_tendsto_pathwiseAveragePayoff_quittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (initial : (quittingGame reward).State) (who : ι) :
    ∀ᵐ play ∂(quittingGame reward).infinitePlayMeasure profile initial,
      Tendsto (fun n => (quittingGame reward).pathwiseAveragePayoff who n play) atTop
        (𝓝 (liminf (fun n => (quittingGame reward).pathwiseAveragePayoff who n play) atTop)) := by
  apply ae_tendsto_pathwiseAveragePayoff_liminf_of_actionIndependent_singleLive
    (quittingGame reward) none ?_ who ?_ profile initial
  · intro state hstate
    cases state with
    | none => exact (hstate rfl).elim
    | some S => exact isAbsorbingState_quittingGame_some reward S
  · intro state first second
    rfl

/-- Actual expected averages converge to expected pathwise liminf at every initial state. -/
theorem tendsto_finiteAveragePayoff_integral_liminf_quittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (initial : (quittingGame reward).State) (who : ι) :
    Tendsto (fun n => (quittingGame reward).finiteAveragePayoff initial n profile who) atTop
      (𝓝 (∫ play, liminf
        (fun n => (quittingGame reward).pathwiseAveragePayoff who n play) atTop
        ∂(quittingGame reward).infinitePlayMeasure profile initial)) :=
  (quittingGame reward).tendsto_finiteAveragePayoff_integral_liminf_of_ae_tendsto
    profile initial who (ae_tendsto_pathwiseAveragePayoff_quittingGame reward profile initial who)

/-- At the live state, literal expected pathwise liminf is the terminal payoff for every profile. -/
theorem integral_liminf_pathwiseAveragePayoff_quittingGame_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    ∫ play, liminf (fun n => (quittingGame reward).pathwiseAveragePayoff who n play) atTop
        ∂(quittingGame reward).infinitePlayMeasure profile none =
      quittingTerminalPayoff reward profile who :=
  tendsto_nhds_unique
    (tendsto_finiteAveragePayoff_integral_liminf_quittingGame reward profile none who)
    (tendsto_finiteAveragePayoff_quittingGame reward profile who)

/-- From an absorbed state, every profile's literal expected pathwise liminf is its reward. -/
theorem integral_liminf_pathwiseAveragePayoff_quittingGame_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (S : {S : Finset ι // S.Nonempty}) (who : ι) :
    ∫ play, liminf (fun n => (quittingGame reward).pathwiseAveragePayoff who n play) atTop
        ∂(quittingGame reward).infinitePlayMeasure profile (some S) = reward S who := by
  have hstage : Tendsto
      (fun n => (quittingGame reward).expectedStagePayoff profile (some S) n who) atTop
      (𝓝 (reward S who)) := by
    simp only [expectedStagePayoff_quittingGame_some]
    exact tendsto_const_nhds
  have haverage : Tendsto
      (fun n => (quittingGame reward).finiteAveragePayoff (some S) n profile who) atTop
      (𝓝 (reward S who)) :=
    hstage.cesaro.congr' (Eventually.of_forall fun n =>
      ((quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff
        profile (some S) who n).symm)
  exact tendsto_nhds_unique
    (tendsto_finiteAveragePayoff_integral_liminf_quittingGame reward profile (some S) who)
    haverage

end GameTheory
