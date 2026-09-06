/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw
import UniformEquilibrium.Quitting.Paths.StageCoalitionMass
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-! # Stage-coalition masses from complete stopping laws -/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The conditional coalition mass at an actual live row is exactly the
finite product-law coalition mass of the extracted live root. -/
theorem quittingLiveRowCoalitionMass_eq_rootCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingLiveRowCoalitionMass reward profile time terminal =
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) terminal.val := by
  let root := quittingProfileLiveRoot reward profile time
  unfold quittingLiveRowCoalitionMass
  change ((pmfPi root)
    (quittingTerminalCoalitionAction terminal)).toReal = _
  rw [pmfPi_apply, ENNReal.toReal_prod]
  have hproduct :
      (∏ x, ((root x)
        (quittingTerminalCoalitionAction terminal x)).toReal) =
        (∏ x ∈ terminal.val, (root x true).toReal) *
          ∏ x ∈ terminal.valᶜ, (1 - (root x true).toReal) := by
    rw [← Finset.prod_mul_prod_compl terminal.val
      (fun x => ((root x)
        (quittingTerminalCoalitionAction terminal x)).toReal)]
    congr 1
    · apply Finset.prod_congr rfl
      intro x hx
      simp [quittingTerminalCoalitionAction, hx]
    · apply Finset.prod_congr rfl
      intro x hx
      have hnot : x ∉ terminal.val := by
        simpa using hx
      have hsum := quittingRoot_continueProbability_add_quitProbability root x
      simp only [quittingTerminalCoalitionAction, hnot, decide_false]
      linarith
  rw [hproduct]
  rfl

/-- Unconditional stage mass factors through survival and the actual live
root's exact coalition mass. -/
theorem quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal =
      quittingLiveMass reward profile time *
        quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) terminal.val := by
  rw [quittingStageCoalitionMass,
    quittingLiveRowCoalitionMass_eq_rootCoalitionMass]

omit [DecidableEq ι] in
/-- The probability of reaching the unique live row is the product of the
players' behavioral hazard survivals. -/
theorem quittingLiveMass_eq_prod_behaviorHazardSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time =
      ∏ who, quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile who)) time := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingLiveMass_succ, ih, quittingJointContinueMass_eq_product]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro who _
      rw [quittingHazardSurvival_succ]
      rfl

/-- An actual stage-coalition mass factors into stopping-law atoms for its
quitters and next-stage hazard survivals for its nonquitters. -/
theorem quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal =
      (∏ who ∈ terminal.val,
        (quittingBehaviorStoppingLaw reward (profile who) (some time)).toReal) *
      ∏ who ∈ terminal.valᶜ,
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward (profile who)) (time + 1) := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_eq_prod_behaviorHazardSurvival]
  unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
  rw [← Finset.prod_mul_prod_compl terminal.val (fun who =>
    quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (profile who)) time)]
  rw [mul_assoc]
  rw [mul_left_comm (∏ who ∈ terminal.valᶜ,
    quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (profile who)) time)]
  rw [← mul_assoc]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply congrArg₂ (fun x y : ℝ => x * y)
  · apply Finset.prod_congr rfl
    intro who _
    rw [quittingBehaviorStoppingLaw_some_toReal,
      quittingHazardStopMass_eq_survival_mul_stop]
    rfl
  · apply Finset.prod_congr rfl
    intro who _
    rw [quittingHazardSurvival_succ]
    have hcontinue := quittingRoot_continueProbability_add_quitProbability
      (quittingProfileLiveRoot reward profile time) who
    change _ * (1 -
      (quittingProfileLiveRoot reward profile time who true).toReal) =
        _ * (quittingProfileLiveRoot reward profile time who false).toReal
    congr 1
    linarith

end GameTheory
