/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Terminal.TerminalAffineReward

/-!
# Nonnegative affine transport of terminal Nash profiles

Nonnegative coordinate scaling transports terminal Nash error playerwise.  A
nonnegative terminal-only shift can then be removed at the sharper cost of
one shift bound: its correction is the shift times actual absorption, so the
prescribed and deviating corrections differ by at most that one bound.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Actual absorption probability belongs to the unit interval. -/
theorem one_sub_quittingLiveMassLimit_mem_Icc
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    1 - quittingLiveMassLimit reward profile ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [show 1 - quittingLiveMassLimit reward profile =
        ∑ S, quittingAbsorbedMassLimit reward profile S by
      linarith [quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile]]
    exact Finset.sum_nonneg fun terminal _ =>
      quittingAbsorbedMassLimit_nonneg reward profile terminal
  · linarith [quittingLiveMassLimit_nonneg reward profile]

/-- Nonnegative playerwise scaling transports terminal Nash error coordinatewise. -/
theorem isεAsymptoticNash_playerwiseScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale : Payoff ι) (profile : (quittingGame reward).BehaviorProfile)
    {ε η : ℝ} (hscale : ∀ who, 0 ≤ scale who)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    (herror : ∀ who, scale who * ε ≤ η) :
    (quittingGame (quittingPlayerwiseAffineReward reward scale 0)).IsεAsymptoticNash
      (quittingTerminalPayoff
        (quittingPlayerwiseAffineReward reward scale 0)) η profile := by
  intro who deviation
  have h := hnash who deviation
  rw [quittingTerminalPayoff_playerwiseAffine,
    quittingTerminalPayoff_playerwiseAffine]
  simp only [Pi.zero_apply, zero_mul, add_zero]
  calc
    scale who * quittingTerminalPayoff reward
          (Function.update profile who deviation) who ≤
        scale who * (quittingTerminalPayoff reward profile who + ε) :=
      mul_le_mul_of_nonneg_left h (hscale who)
    _ ≤ scale who * quittingTerminalPayoff reward profile who + η := by
      linarith [herror who]

/-- Removing a bounded nonnegative terminal-only shift costs only one shift
bound, because both prescribed and deviating shift corrections are actual
absorption probabilities in `[0,1]`. -/
theorem IsεAsymptoticNash.of_nonnegative_terminalShift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (shift : Payoff ι) (profile : (quittingGame reward).BehaviorProfile)
    {ε shiftBound : ℝ} (hshift : ∀ who, 0 ≤ shift who)
    (hshiftBound : ∀ who, shift who ≤ shiftBound)
    (hnash :
      (quittingGame (quittingPlayerwiseAffineReward reward 1 shift)).IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPlayerwiseAffineReward reward 1 shift)) ε profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (ε + shiftBound) profile := by
  intro who deviation
  have h := hnash who deviation
  rw [quittingTerminalPayoff_playerwiseAffine,
    quittingTerminalPayoff_playerwiseAffine] at h
  simp only [Pi.one_apply, one_mul] at h
  have hplan := one_sub_quittingLiveMassLimit_mem_Icc reward profile
  have hdeviation := one_sub_quittingLiveMassLimit_mem_Icc reward
    (Function.update profile who deviation)
  have hplanShift : shift who *
      (1 - quittingLiveMassLimit reward profile) ≤ shiftBound := by
    calc
      shift who * (1 - quittingLiveMassLimit reward profile) ≤ shift who :=
        mul_le_of_le_one_right (hshift who) hplan.2
      _ ≤ shiftBound := hshiftBound who
  have hdeviationShift : 0 ≤ shift who *
      (1 - quittingLiveMassLimit reward
        (Function.update profile who deviation)) :=
    mul_nonneg (hshift who) hdeviation.1
  calc
    quittingTerminalPayoff reward
          (Function.update profile who deviation) who ≤
        quittingTerminalPayoff reward
            (Function.update profile who deviation) who +
          shift who * (1 - quittingLiveMassLimit reward
            (Function.update profile who deviation)) :=
      le_add_of_nonneg_right hdeviationShift
    _ ≤ quittingTerminalPayoff reward profile who +
          shift who * (1 - quittingLiveMassLimit reward profile) + ε := h
    _ ≤ quittingTerminalPayoff reward profile who + shiftBound + ε := by
      linarith
    _ = quittingTerminalPayoff reward profile who + (ε + shiftBound) := by
      ring

/-- The scaling transfer preserves one literal root sequence and every
restart; only the reward parameter of its profile is changed. -/
theorem quittingRootSequence_allSuffix_terminalNash_playerwiseScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale : Payoff ι) (roots : ℕ → ι → PMF Bool)
    {ε η : ℝ} (hscale : ∀ who, 0 ≤ scale who)
    (hnash : ∀ start,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingRootSequenceProfile reward roots start))
    (herror : ∀ who, scale who * ε ≤ η) :
    ∀ start,
      (quittingGame (quittingPlayerwiseAffineReward reward scale 0)).IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPlayerwiseAffineReward reward scale 0)) η
        (quittingRootSequenceProfile
          (quittingPlayerwiseAffineReward reward scale 0) roots start) := by
  intro start
  rw [← quittingRootSequenceProfile_congr_reward reward
    (quittingPlayerwiseAffineReward reward scale 0) roots start]
  exact isεAsymptoticNash_playerwiseScale reward scale
    (quittingRootSequenceProfile reward roots start) hscale (hnash start) herror

/-- The sharp shift-back transfer preserves one literal root sequence and
every restart. -/
theorem quittingRootSequence_allSuffix_terminalNash_of_nonnegative_terminalShift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (shift : Payoff ι) (roots : ℕ → ι → PMF Bool)
    {ε shiftBound : ℝ} (hshift : ∀ who, 0 ≤ shift who)
    (hshiftBound : ∀ who, shift who ≤ shiftBound)
    (hnash : ∀ start,
      (quittingGame (quittingPlayerwiseAffineReward reward 1 shift)).IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingPlayerwiseAffineReward reward 1 shift)) ε
        (quittingRootSequenceProfile
          (quittingPlayerwiseAffineReward reward 1 shift) roots start)) :
    ∀ start,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε + shiftBound)
        (quittingRootSequenceProfile reward roots start) := by
  intro start
  apply IsεAsymptoticNash.of_nonnegative_terminalShift reward shift
    (quittingRootSequenceProfile reward roots start) hshift hshiftBound
  rw [quittingRootSequenceProfile_congr_reward reward
    (quittingPlayerwiseAffineReward reward 1 shift) roots start]
  exact hnash start

end GameTheory
