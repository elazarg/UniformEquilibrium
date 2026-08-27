/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectTelescope
import UniformEquilibrium.Quitting.Root.SelfTailClosure

/-!
# Terminal-semantic identities for self-tail closure

The literal self-tail closure preserves every unconditional coalition atom at
the copied marked date.  Strictly after that date its complete all-Continue
continuation is the original profile, so its terminal-semantic pair and spine
debt excess are exact identities rather than approximation statements.

No equilibrium, cap-Nash, or near-minimality property is transferred to the
closed profile.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- Live probability through a displayed date depends only on the actual live
roots at the strictly earlier dates. -/
theorem quittingLiveMass_eq_of_liveRoot_eq_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (stage : ℕ)
    (hroot : ∀ time < stage,
      quittingProfileLiveRoot reward first time =
        quittingProfileLiveRoot reward second time) :
    quittingLiveMass reward first stage =
      quittingLiveMass reward second stage := by
  induction stage with
  | zero => rw [quittingLiveMass_zero, quittingLiveMass_zero]
  | succ stage ih =>
      rw [quittingLiveMass_succ, quittingLiveMass_succ,
        ih (fun time htime => hroot time (by omega)),
        quittingJointContinueMass_eq_product,
        quittingJointContinueMass_eq_product]
      congr 1
      apply Finset.prod_congr rfl
      intro player _
      exact congrArg (fun law : PMF Bool => (law false).toReal)
        (congrFun (hroot stage (by omega)) player)

variable [DecidableEq ι]

/-- Two actual profiles with the same live roots through a displayed date have
the same unconditional terminal-coalition atom at that date. -/
theorem quittingStageCoalitionMass_eq_of_liveRoot_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hroot : ∀ time ≤ stage,
      quittingProfileLiveRoot reward first time =
        quittingProfileLiveRoot reward second time) :
    quittingStageCoalitionMass reward first stage terminal =
      quittingStageCoalitionMass reward second stage terminal := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_eq_of_liveRoot_eq_of_lt reward first second stage
      (fun time htime => hroot time htime.le),
    hroot stage le_rfl]

/-- Copying the actual live roots through `stage` preserves every exact
unconditional coalition atom at that stage. -/
theorem quittingStageCoalitionMass_selfTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingSelfTailClosure reward profile stage) stage terminal =
      quittingStageCoalitionMass reward profile stage terminal := by
  apply quittingStageCoalitionMass_eq_of_liveRoot_eq_of_le
  intro time htime
  exact quittingProfileLiveRoot_selfTailClosure_eq_of_le
    reward profile stage time htime

/-- Restarting an arbitrary behavioral tail after a copied live-root prefix
preserves every unconditional coalition atom at the final copied date. -/
theorem quittingStageCoalitionMass_crossTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefixProfile tailProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingCrossTailClosure reward prefixProfile tailProfile stage)
        stage terminal =
      quittingStageCoalitionMass reward prefixProfile stage terminal := by
  apply quittingStageCoalitionMass_eq_of_liveRoot_eq_of_le
  intro time htime
  exact quittingProfileLiveRoot_crossTailClosure_eq_of_le
    reward prefixProfile tailProfile stage time htime

/-- The post-date terminal-semantic pair of a self-tail closure is exactly the
pair of the original complete profile. -/
theorem quittingTerminalSemanticPair_spine_selfTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (quittingSelfTailClosure reward profile stage) (stage + 1)) =
      quittingTerminalSemanticPair reward profile := by
  rw [quittingAllContinueProfileSpine_selfTailClosure]

/-- The post-date terminal-semantic pair of a cross-tail closure is exactly
the pair of the independently restarted tail profile. -/
theorem quittingTerminalSemanticPair_spine_crossTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefixProfile tailProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (quittingCrossTailClosure reward prefixProfile tailProfile stage)
          (stage + 1)) =
      quittingTerminalSemanticPair reward tailProfile := by
  rw [quittingAllContinueProfileSpine_crossTailClosure]

/-- The post-date spine debt excess of a self-tail closure is exactly the
original profile's literal total debt minus the displayed reference level. -/
theorem quittingSpineDebtExcess_selfTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (reference : ℝ) :
    quittingSpineDebtExcess reward
        (quittingSelfTailClosure reward profile stage) reference (stage + 1) =
      quittingTerminalDebtSum reward profile - reference := by
  unfold quittingSpineDebtExcess
  rw [quittingAllContinueProfileSpine_selfTailClosure]
  rfl

/-- The post-date spine debt excess of a cross-tail closure is exactly the
restarted tail profile's total debt minus the displayed reference level. -/
theorem quittingSpineDebtExcess_crossTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefixProfile tailProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (reference : ℝ) :
    quittingSpineDebtExcess reward
        (quittingCrossTailClosure reward prefixProfile tailProfile stage)
        reference (stage + 1) =
      quittingTerminalDebtSum reward tailProfile - reference := by
  unfold quittingSpineDebtExcess
  rw [quittingAllContinueProfileSpine_crossTailClosure]
  rfl

end GameTheory
