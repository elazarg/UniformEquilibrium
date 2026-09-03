/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingExploitabilityRetraction

/-!
# Period-preserving passive-player padding retraction

Canonical passive-player padding and its quiet lift act pointwise on the live
root sequence.  Consequently they preserve every literal period of that
sequence.  This file records that fact together with the multiplier form of
the pointwise exploitability retraction.  All deviations in the
exploitability comparison remain unrestricted behavioral deviations.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- Projecting a padded profile preserves every literal period of its live
root sequence. -/
theorem Function.Periodic.quittingPassivePaddingProjectProfile
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ) (penalty : ℝ)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward upper penalty)).BehaviorProfile)
    {period : ℕ}
    (hperiodic : Function.Periodic
      (quittingProfileLiveRoot
        (quittingPassivePaddingReward (J := J) reward upper penalty) profile)
      period) :
    Function.Periodic
      (quittingProfileLiveRoot reward
        (quittingPassivePaddingProjectProfile reward profile)) period := by
  rw [quittingProfileLiveRoot_passivePaddingProjectProfile]
  intro time
  funext old
  exact congrFun (hperiodic time) (.inl old)

/-- Quietly lifting an old profile preserves every literal period of its live
root sequence. -/
theorem Function.Periodic.quittingPassivePaddingQuietProfile
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (penalty : ℝ)
    (profile : (quittingGame reward).BehaviorProfile) {period : ℕ}
    (hperiodic : Function.Periodic
      (quittingProfileLiveRoot reward profile) period) :
    Function.Periodic
      (quittingProfileLiveRoot
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (quittingPassivePaddingQuietProfile (J := J) reward penalty profile))
      period := by
  rw [quittingProfileLiveRoot_passivePaddingQuietProfile]
  intro time
  funext player
  cases player with
  | inl old => exact congrFun (hperiodic time) old
  | inr fresh => rfl

/-- Multiplier form of the pointwise exploitability retraction. -/
theorem quittingTerminalExploitability_project_passivePadding_le_multiplier
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile) :
    quittingTerminalExploitability reward
        (quittingPassivePaddingProjectProfile reward profile) ≤
      quittingPassivePaddingRetractionMultiplier (J := J) reward penalty *
        quittingTerminalExploitability
          (quittingPassivePaddingReward (J := J) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty) profile := by
  let factor := quittingPassivePaddingRetractionFactor (J := J) reward penalty
  let multiplier := quittingPassivePaddingRetractionMultiplier (J := J) reward penalty
  have hmultiplier : 0 ≤ multiplier := by
    have hplayers : 0 ≤ (Fintype.card J : ℝ) := by positivity
    have hwidth := quittingPassivePaddingWidth_nonneg reward
    unfold multiplier quittingPassivePaddingRetractionMultiplier
    positivity
  have hretract :=
    retractionFactor_mul_quittingTerminalExploitability_project_le
      (J := J) reward hpenalty profile
  calc
    quittingTerminalExploitability reward
        (quittingPassivePaddingProjectProfile reward profile) =
      multiplier * (factor * quittingTerminalExploitability reward
        (quittingPassivePaddingProjectProfile reward profile)) := by
          rw [← mul_assoc, mul_comm multiplier factor,
            quittingPassivePaddingRetractionFactor_mul_multiplier
              (J := J) reward hpenalty, one_mul]
    _ ≤ multiplier * quittingTerminalExploitability
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty) profile :=
      mul_le_mul_of_nonneg_left hretract hmultiplier

/-- For one fresh player, the multiplier is literally `1 + width / penalty`.
This includes the zero-width case. -/
theorem quittingTerminalExploitability_project_onePassivePlayer_le
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    (profile : (quittingGame
      (quittingPassivePaddingReward (J := PUnit) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)).BehaviorProfile) :
    quittingTerminalExploitability reward
        (quittingPassivePaddingProjectProfile reward profile) ≤
      (1 + quittingPassivePaddingWidth reward / penalty) *
        quittingTerminalExploitability
          (quittingPassivePaddingReward (J := PUnit) reward
            (quittingPassivePaddingUpperEndpoint reward) penalty) profile := by
  simpa [quittingPassivePaddingRetractionMultiplier] using
    (quittingTerminalExploitability_project_passivePadding_le_multiplier
      (J := PUnit) reward hpenalty profile)

end GameTheory
