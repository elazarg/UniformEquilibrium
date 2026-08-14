/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Adaptive.PotentialSystem
import UniformEquilibrium.Certificates.Public.PublicResponseEnforcementLedger

/-!
# Enforcement ledgers from adaptive systems

This file converts an expectation-level adaptive system on a fixed behavior
profile to an operational public-response ledger. The monitoring residual is
the exact realized stage-payoff gap from the target, so the historywise
deviation inequality holds by equality rather than as an extra premise.

The price is a factor two in the error: one copy comes from the initial
potential displacement and one from the adaptive charge budget.  Analytic
or recursive data do not enter this conversion. They must first construct
the adaptive system by an independent argument.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- Regard an arbitrary behavior profile as a public-phase profile by storing
the complete public history in the phase. -/
def behaviorPublicPhaseProfile (profile : G.BehaviorProfile) :
    G.PublicPhaseProfile where
  Phase := Σ time, G.Hist time
  phase := fun time history => ⟨time, history⟩
  play := fun phase who => profile who phase.1 phase.2

@[simp]
theorem behaviorPublicPhaseProfile_behaviorProfile
    (profile : G.BehaviorProfile) :
    (G.behaviorPublicPhaseProfile profile).behaviorProfile = profile := by
  rfl

namespace AdaptivePotentialSystemAt

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]
  {profile : G.BehaviorProfile} {initial : G.State}
  {target : Payoff ι} {error : ℝ}

/-- Canonical operational ledger extracted from an expectation-level adaptive
system on the same behavior profile.

All historywise stage inequalities are proved from the definitions of the
three exact stage gaps.  In particular, no historywise deviation inequality
is an input to this constructor. -/
def toExactStageGapPublicResponseEnforcementLedgerAt
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (herror : 0 ≤ error) :
    G.PublicResponseEnforcementLedgerAt
      (G.behaviorPublicPhaseProfile profile) initial target
      (2 * error) where
  horizon := system.horizon
  lowerLoss := fun who time history =>
    target who - G.stageEUAt profile history who
  upperLoss := fun who time history =>
    G.stageEUAt profile history who - target who
  monitoringResidual := fun who deviation time history =>
    G.stageEUAt (Function.update profile who deviation) history who -
      target who
  continuationResidual := fun _ _ _ _ => 0
  monitoringError := 2 * error
  continuationError := 0
  error_nonneg := by
    linarith
  horizon_ge_two := system.horizon_ge_two
  lower_stage := by
    intro who time history
    simp only [behaviorPublicPhaseProfile_behaviorProfile]
    linarith
  upper_stage := by
    intro who time history
    simp only [behaviorPublicPhaseProfile_behaviorProfile]
    linarith
  deviation_stage := by
    intro who deviation time history
    simp only [behaviorPublicPhaseProfile_behaviorProfile]
    linarith
  lowerLoss_cesaro := by
    intro who total htotal
    simp only [behaviorPublicPhaseProfile_behaviorProfile]
    have hpay :=
      system.abs_finiteAveragePayoff_sub_target_le_two_mul_error
        who total htotal
    rw [abs_le] at hpay
    have htotal_pos : 0 < total := by
      have hhorizon := system.horizon_ge_two
      omega
    have heq :
        (total : ℝ)⁻¹ *
            ∑ time ∈ Finset.range total,
              G.expectedHistoryValue profile initial
                (fun time history =>
                  target who - G.stageEUAt profile history who)
                time =
          target who -
            G.finiteAveragePayoff initial total profile who := by
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      simp only [expectedHistoryValue, expectedStagePayoff,
        expect_sub, expect_const, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt htotal_pos)]
    rw [heq]
    linarith
  upperLoss_cesaro := by
    intro who total htotal
    simp only [behaviorPublicPhaseProfile_behaviorProfile]
    have hpay :=
      system.abs_finiteAveragePayoff_sub_target_le_two_mul_error
        who total htotal
    rw [abs_le] at hpay
    have htotal_pos : 0 < total := by
      have hhorizon := system.horizon_ge_two
      omega
    have heq :
        (total : ℝ)⁻¹ *
            ∑ time ∈ Finset.range total,
              G.expectedHistoryValue profile initial
                (fun time history =>
                  G.stageEUAt profile history who - target who)
                time =
          G.finiteAveragePayoff initial total profile who -
            target who := by
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      simp only [expectedHistoryValue, expectedStagePayoff,
        expect_sub, expect_const, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt htotal_pos)]
    rw [heq]
    exact hpay.2
  monitoringResidual_cesaro := by
    intro who deviation total htotal
    simp only [behaviorPublicPhaseProfile_behaviorProfile]
    have hpay :=
      system.finiteAveragePayoff_update_le_target_add_two_mul_error
        who deviation total htotal
    have htotal_pos : 0 < total := by
      have hhorizon := system.horizon_ge_two
      omega
    have heq :
        (total : ℝ)⁻¹ *
            ∑ time ∈ Finset.range total,
              G.expectedHistoryValue
                (Function.update profile who deviation) initial
                (fun time history =>
                  G.stageEUAt
                      (Function.update profile who deviation)
                      history who -
                    target who)
                time =
          G.finiteAveragePayoff initial total
              (Function.update profile who deviation) who -
            target who := by
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      simp only [expectedHistoryValue, expectedStagePayoff,
        expect_sub, expect_const, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt htotal_pos)]
    rw [heq]
    linarith
  continuationResidual_cesaro := by
    intro who deviation total htotal
    simp [expectedHistoryValue]
  deviation_budget := by
    linarith

end AdaptivePotentialSystemAt

end StochasticGame
end GameTheory
