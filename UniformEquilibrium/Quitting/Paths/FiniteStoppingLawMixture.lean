/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Analysis.Nash
import MathUE.Probability.StoppingLawReconstruction
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Paths.StoppingLawMixture

/-!
# Behavioral realization of finite stopping-law mixtures

A finite law over complete behavioral strategies induces a finite mixture of
their quit-time laws.  Reconstructing its conditional hazard gives one
ordinary behavioral strategy with exactly that mixed stopping law.  Terminal
payoff is affine in this mixture for every payoff observer, including an
observer different from the player whose strategy is mixed.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction
open Math.Probability.DiscreteHazard
open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Replace every reward coordinate by one fixed observer's coordinate. -/
def quittingObserverReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (observer : ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun S _ => reward S observer

omit [DecidableEq ι] in
/-- The observer-reward table reads exactly the original observer payoff. -/
theorem quittingTerminalPayoff_observerReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer player : ι) :
    quittingTerminalPayoff (quittingObserverReward reward observer)
        profile player =
      quittingTerminalPayoff reward profile observer := by
  unfold quittingTerminalPayoff
  apply Finset.sum_congr rfl
  intro S _
  rw [QuittingLCPClassification.quittingAbsorbedMassLimit_congr_reward
    (quittingObserverReward reward observer) reward profile S]
  rfl

/-- Binary stopping-law mixing is affine for any payoff observer, not just
the player whose clock is being mixed. -/
theorem quittingTerminalPayoff_update_stoppingLawMixture_observer_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mixer observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mixer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingStoppingLawMixtureBehaviorStrategy reward mixer source target
            lambda hlambda0 hlambda1)) observer =
      (1 - lambda) * quittingTerminalPayoff reward
          (Function.update profile mixer source) observer +
        lambda * quittingTerminalPayoff reward
          (Function.update profile mixer target) observer := by
  let observerReward := quittingObserverReward reward observer
  have haffine := quittingTerminalPayoff_update_stoppingLawMixture_eq
    observerReward profile mixer source target lambda hlambda0 hlambda1
  rw [quittingTerminalPayoff_observerReward reward _ observer mixer,
    quittingTerminalPayoff_observerReward reward _ observer mixer,
    quittingTerminalPayoff_observerReward reward _ observer mixer] at haffine
  exact haffine

/-- The mixture of the complete stopping laws in a finite strategy law. -/
def quittingFiniteStrategyStoppingLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι)
    (mixture : FinDist ((quittingGame reward).BehaviorStrategy who)) :
    PMF (Option ℕ) :=
  mixture.toPMF.bind fun strategy =>
    quittingBehaviorStoppingLaw reward strategy

/-- One ordinary behavioral strategy reconstructed from a finite mixture of
complete stopping laws. -/
def quittingFiniteStoppingLawMixtureBehaviorStrategy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι)
    (mixture : FinDist ((quittingGame reward).BehaviorStrategy who)) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time _ =>
    (StoppingLaw.toScalarHazard
      (quittingFiniteStrategyStoppingLaw reward who mixture)).toBoolean time

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorLiveHazard_finiteStoppingLawMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι)
    (mixture : FinDist ((quittingGame reward).BehaviorStrategy who)) :
    quittingBehaviorLiveHazard reward
        (quittingFiniteStoppingLawMixtureBehaviorStrategy reward who mixture) =
      (StoppingLaw.toScalarHazard
        (quittingFiniteStrategyStoppingLaw reward who mixture)).toBoolean := by
  rfl

omit [DecidableEq ι] in
/-- The reconstructed behavior has exactly the requested finite mixture of
complete stopping laws. -/
@[simp] theorem quittingBehaviorStoppingLaw_finiteStoppingLawMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι)
    (mixture : FinDist ((quittingGame reward).BehaviorStrategy who)) :
    quittingBehaviorStoppingLaw reward
        (quittingFiniteStoppingLawMixtureBehaviorStrategy reward who mixture) =
      quittingFiniteStrategyStoppingLaw reward who mixture := by
  unfold quittingBehaviorStoppingLaw quittingHazardStoppingLaw
  rw [quittingBehaviorLiveHazard_finiteStoppingLawMixture,
    ScalarHazard.toScalar_toBoolean,
    StoppingLaw.stoppingLaw_toScalarHazard]

/-- Terminal payoff to any observer is the finite expectation of the payoffs
generated by the component strategies. -/
theorem quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mixer observer : ι)
    (mixture : FinDist ((quittingGame reward).BehaviorStrategy mixer)) :
    quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer mixture))
        observer =
      mixture.expect fun strategy =>
        quittingTerminalPayoff reward
          (Function.update profile mixer strategy) observer := by
  let observerReward := quittingObserverReward reward observer
  let value : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update profile mixer
        (quittingPureTimeBehaviorStrategy reward mixer choice)) observer
  obtain ⟨M, -, hreward⟩ := exists_quittingRewardBound reward
  have hvalue : ∀ choice, |value choice| ≤ M := by
    intro choice
    exact abs_quittingTerminalPayoff_le reward _ observer hreward
  have hmixture := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    observerReward profile mixer
      (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer mixture)
  rw [quittingTerminalPayoff_observerReward reward _ observer mixer] at hmixture
  calc
    quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer mixture))
        observer =
      Math.Probability.expect
        (quittingBehaviorStoppingLaw observerReward
          (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer mixture))
        (fun choice =>
          quittingTerminalPayoff observerReward
            (Function.update profile mixer
              (quittingPureTimeBehaviorStrategy observerReward mixer choice))
            mixer) := hmixture
    _ = mixture.expect fun strategy =>
        quittingTerminalPayoff reward
          (Function.update profile mixer strategy) observer := by
      rw [show quittingBehaviorStoppingLaw observerReward
          (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer mixture) =
          quittingBehaviorStoppingLaw reward
            (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer mixture) by
        rfl]
      have hvalueEq : (fun choice =>
          quittingTerminalPayoff observerReward
            (Function.update profile mixer
              (quittingPureTimeBehaviorStrategy observerReward mixer choice))
            mixer) = value := by
        funext choice
        rw [quittingTerminalPayoff_observerReward reward _ observer mixer]
        rfl
      rw [hvalueEq]
      change Math.Probability.expect
          (quittingBehaviorStoppingLaw reward
            (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer mixture))
          value = _
      rw [quittingBehaviorStoppingLaw_finiteStoppingLawMixture]
      unfold quittingFiniteStrategyStoppingLaw
      rw [Math.Probability.expect_bind_of_bounded _ _ value hvalue]
      unfold FinDist.expect FinDist.prob
      apply tsum_congr
      intro strategy
      congr 1
      have hcomponent :=
        quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
          observerReward profile mixer strategy
      rw [quittingTerminalPayoff_observerReward reward _ observer mixer] at hcomponent
      rw [← hvalueEq]
      change Math.Probability.expect
          (quittingBehaviorStoppingLaw observerReward (who := mixer) strategy)
          (fun choice =>
            quittingTerminalPayoff observerReward
              (Function.update profile mixer
                (quittingPureTimeBehaviorStrategy observerReward mixer choice))
              mixer) = _
      exact hcomponent.symm

end GameTheory
