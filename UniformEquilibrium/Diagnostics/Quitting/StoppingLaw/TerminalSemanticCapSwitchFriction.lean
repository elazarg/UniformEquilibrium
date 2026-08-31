/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawFiniteSplice
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

/-!
# Deleted-survival friction for a stopping-law cap switch

This module normalizes a pair of pure stopping times at their first
disagreement and bounds the change of their payoff gap when one opponent's
complete stopping law is mixed.  The sharp estimate retains both the
opponents outside the observer/mover pair and the mover's inclusive
post-mark tail.

The estimates are static stopping-law geometry.  They do not assert that a
reset edge is chronological play, produce a reset square, or consume the
resulting paid row.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.Probability.DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- The payoff difference between quitting at `start` and a normalized plan
which first differs there by waiting strictly longer (or forever). -/
def quittingNormalizedPureTimeGap
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : iota) (start : ℕ) (later : Option ℕ) : ℝ :=
  quittingPureTimeDeviationPayoff reward profile observer (some start) -
    quittingPureTimeDeviationPayoff reward profile observer
      (quittingAbsolutePureTime start later)

/-- The normalized gap is exactly opponent survival to the disagreement row
times the reached Quit-versus-wait difference. -/
theorem quittingNormalizedPureTimeGap_eq_opponentSurvival_mul
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : iota) (start : ℕ) (later : Option ℕ) :
    quittingNormalizedPureTimeGap reward profile observer start later =
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) observer 0 start *
        (quittingFixedOpponentsQuitValue reward
            (quittingProfileLiveRoot reward profile) observer start -
          quittingRootSequenceRelativePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward profile) observer start later) := by
  unfold quittingNormalizedPureTimeGap quittingPureTimeDeviationPayoff
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  exact quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
    reward (quittingProfileLiveRoot reward profile) observer start later

private theorem abs_quittingFixedOpponentsQuitValue_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (roots : ℕ → iota → PMF Bool) (observer : iota) (start : ℕ)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingFixedOpponentsQuitValue reward roots observer start| ≤ bound := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward roots observer (0 : Payoff iota) start]
  exact abs_quittingRootExpectedPayoff_le_bound reward (0 : Payoff iota)
    (Function.update (roots start) observer (PMF.pure true)) observer
      hreward (fun _ ↦ by simpa using hbound)

private theorem abs_relativePureTimeTerminalValue_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (roots : ℕ → iota → PMF Bool) (observer : iota) (start : ℕ)
    (later : Option ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingRootSequenceRelativePureTimeTerminalValue
        reward roots observer start later| ≤ bound := by
  unfold quittingRootSequenceRelativePureTimeTerminalValue
    quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  exact abs_quittingRootSequenceTerminalValue_le reward
    (quittingRootSequenceUpdate roots observer
      (quittingPureTimeHazard (quittingAbsolutePureTime start later)))
    observer start hbound hreward

/-- A normalized pure-time gap is screened by full opponent survival to its
disagreement row. -/
theorem abs_quittingNormalizedPureTimeGap_le_opponentSurvival
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : iota) (start : ℕ) (later : Option ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingNormalizedPureTimeGap reward profile observer start later| ≤
      2 * bound * quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) observer 0 start := by
  let roots := quittingProfileLiveRoot reward profile
  let reached := quittingFixedOpponentsQuitValue reward roots observer start -
    quittingRootSequenceRelativePureTimeTerminalValue
      reward roots observer start later
  have hquit := abs_quittingFixedOpponentsQuitValue_le
    reward roots observer start bound hbound hreward
  have hlater := abs_relativePureTimeTerminalValue_le
    reward roots observer start later bound hbound hreward
  have hreached : |reached| ≤ 2 * bound := by
    calc
      |reached| ≤
          |quittingFixedOpponentsQuitValue reward roots observer start| +
            |quittingRootSequenceRelativePureTimeTerminalValue
              reward roots observer start later| := abs_sub _ _
      _ ≤ bound + bound := add_le_add hquit hlater
      _ = 2 * bound := by ring
  have hlive : 0 ≤ quittingOpponentSurvivalWeight roots observer 0 start :=
    quittingOpponentSurvivalWeight_nonneg roots observer 0 start
  rw [quittingNormalizedPureTimeGap_eq_opponentSurvival_mul, abs_mul,
    abs_of_nonneg hlive]
  change quittingOpponentSurvivalWeight roots observer 0 start * |reached| ≤
    2 * bound * quittingOpponentSurvivalWeight roots observer 0 start
  simpa [mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hreached hlive

/-- A normalized gap is bounded by the pair-deleted survival, the mover's
own inclusive survival, and the two-sided terminal reward bound. -/
theorem abs_quittingNormalizedPureTimeGap_le_pairDeleted_mul_moverSurvival
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota) (hmoverObserver : mover ≠ observer)
    (start : ℕ) (later : Option ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingNormalizedPureTimeGap reward profile observer start later| ≤
      2 * bound *
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start *
        quittingHazardSurvival
          (fun time ↦ quittingProfileLiveRoot reward profile time mover) start := by
  let roots := quittingProfileLiveRoot reward profile
  let reached := quittingFixedOpponentsQuitValue reward roots observer start -
    quittingRootSequenceRelativePureTimeTerminalValue
      reward roots observer start later
  have hquit := abs_quittingFixedOpponentsQuitValue_le
    reward roots observer start bound hbound hreward
  have hlater := abs_relativePureTimeTerminalValue_le
    reward roots observer start later bound hbound hreward
  have hreached : |reached| ≤ 2 * bound := by
    calc
      |reached| ≤
          |quittingFixedOpponentsQuitValue reward roots observer start| +
            |quittingRootSequenceRelativePureTimeTerminalValue
              reward roots observer start later| := by
                exact abs_sub _ _
      _ ≤ bound + bound := add_le_add hquit hlater
      _ = 2 * bound := by ring
  have hdeleted : 0 ≤ quittingPairDeletedSurvivalWeight
      roots mover observer 0 start :=
    quittingPairDeletedSurvivalWeight_nonneg roots mover observer 0 start
  have hmover : 0 ≤ quittingHazardSurvival
      (fun time ↦ roots time mover) start :=
    quittingHazardSurvival_nonneg _ _
  rw [quittingNormalizedPureTimeGap_eq_opponentSurvival_mul,
    quittingOpponentSurvivalWeight_eq_pairDeleted_mul_moverSurvival
      roots mover observer hmoverObserver start]
  change |(_ * _) * reached| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg hdeleted, abs_of_nonneg hmover]
  have hscaled := mul_le_mul_of_nonneg_left hreached
    (mul_nonneg hdeleted hmover)
  nlinarith

/-- Updating the mover by a complete stopping-law mixture makes the
normalized pure-time gap exactly affine in the mixing scale. -/
theorem quittingNormalizedPureTimeGap_update_stoppingLawMixture_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (scale : ℝ) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1)
    (start : ℕ) (later : Option ℕ) :
    quittingNormalizedPureTimeGap reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            scale hscale0 hscale1)) observer start later =
      (1 - scale) * quittingNormalizedPureTimeGap reward
          (Function.update profile mover source) observer start later +
        scale * quittingNormalizedPureTimeGap reward
          (Function.update profile mover target) observer start later := by
  have hpayoff (quitTime : Option ℕ) :
      quittingPureTimeDeviationPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              scale hscale0 hscale1)) observer quitTime =
        (1 - scale) * quittingPureTimeDeviationPayoff reward
            (Function.update profile mover source) observer quitTime +
          scale * quittingPureTimeDeviationPayoff reward
            (Function.update profile mover target) observer quitTime := by
    let deviation := quittingPureTimeBehaviorStrategy reward observer quitTime
    have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
      reward (Function.update profile observer deviation) mover observer
        source target scale hscale0 hscale1
    have hmixed :
        Function.update (Function.update profile observer deviation) mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              scale hscale0 hscale1) =
          Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                scale hscale0 hscale1)) observer deviation :=
      Function.update_comm (Ne.symm hmoverObserver) deviation
        (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
          scale hscale0 hscale1) profile
    have hsource :
        Function.update (Function.update profile observer deviation) mover source =
          Function.update (Function.update profile mover source) observer deviation :=
      Function.update_comm (Ne.symm hmoverObserver) deviation source profile
    have htarget :
        Function.update (Function.update profile observer deviation) mover target =
          Function.update (Function.update profile mover target) observer deviation :=
      Function.update_comm (Ne.symm hmoverObserver) deviation target profile
    rw [hmixed, hsource, htarget] at haffine
    exact haffine
  unfold quittingNormalizedPureTimeGap
  rw [hpayoff, hpayoff]
  ring

private theorem abs_quittingNormalizedPureTimeGap_update_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota) (hmoverObserver : mover ≠ observer)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (start : ℕ) (later : Option ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingNormalizedPureTimeGap reward
        (Function.update profile mover strategy) observer start later| ≤
      2 * bound *
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward strategy) start := by
  have hbound' :=
    abs_quittingNormalizedPureTimeGap_le_pairDeleted_mul_moverSurvival
      reward (Function.update profile mover strategy) mover observer
        hmoverObserver start later bound hbound hreward
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate] at hbound'
  simpa [quittingRootSequenceUpdate] using hbound'

/-- **Sharp deleted-survival friction.** The gap change along a complete-law
mixture is bounded by the mover-deleted survival times the sum of the two
endpoint inclusive tails. -/
theorem abs_quittingNormalizedPureTimeGap_update_stoppingLawMixture_sub_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (scale : ℝ) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1)
    (start : ℕ) (later : Option ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingNormalizedPureTimeGap reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              scale hscale0 hscale1)) observer start later -
        quittingNormalizedPureTimeGap reward
          (Function.update profile mover source) observer start later| ≤
      2 * bound * scale *
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start *
        (StoppingLaw.survival
            (quittingBehaviorStoppingLaw reward source) start +
          StoppingLaw.survival
            (quittingBehaviorStoppingLaw reward target) start) := by
  let mixed := quittingStoppingLawMixtureBehaviorStrategy reward mover source target
    scale hscale0 hscale1
  let sourceGap := quittingNormalizedPureTimeGap reward
    (Function.update profile mover source) observer start later
  let targetGap := quittingNormalizedPureTimeGap reward
    (Function.update profile mover target) observer start later
  have hsource := abs_quittingNormalizedPureTimeGap_update_le
    reward profile mover observer hmoverObserver source start later
      bound hbound hreward
  have htarget := abs_quittingNormalizedPureTimeGap_update_le
    reward profile mover observer hmoverObserver target start later
      bound hbound hreward
  have hsub : |targetGap - sourceGap| ≤
      2 * bound *
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start *
        (quittingHazardSurvival
            (quittingBehaviorLiveHazard reward source) start +
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward target) start) := by
    calc
      |targetGap - sourceGap| ≤ |targetGap| + |sourceGap| := abs_sub _ _
      _ ≤
          2 * bound *
              quittingPairDeletedSurvivalWeight
                (quittingProfileLiveRoot reward profile) mover observer 0 start *
              quittingHazardSurvival
                (quittingBehaviorLiveHazard reward target) start +
            2 * bound *
              quittingPairDeletedSurvivalWeight
                (quittingProfileLiveRoot reward profile) mover observer 0 start *
              quittingHazardSurvival
                (quittingBehaviorLiveHazard reward source) start := by
                  exact add_le_add htarget hsource
      _ = _ := by ring
  have haffine :=
    quittingNormalizedPureTimeGap_update_stoppingLawMixture_eq
      reward profile mover observer hmoverObserver source target scale
        hscale0 hscale1 start later
  have hdifference :
      quittingNormalizedPureTimeGap reward
            (Function.update profile mover mixed) observer start later -
          sourceGap = scale * (targetGap - sourceGap) := by
    dsimp only [mixed, sourceGap, targetGap]
    rw [haffine]
    ring
  rw [show quittingStoppingLawMixtureBehaviorStrategy reward mover source target
      scale hscale0 hscale1 = mixed by rfl, hdifference, abs_mul,
    abs_of_nonneg hscale0]
  have hscaled := mul_le_mul_of_nonneg_left hsub hscale0
  rw [stoppingLawSurvival_quittingBehaviorStoppingLaw,
    stoppingLawSurvival_quittingBehaviorStoppingLaw]
  nlinarith

/-- The scale-only consequence of the sharp friction bound. -/
theorem abs_quittingNormalizedPureTimeGap_update_stoppingLawMixture_sub_le_coarse
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota) (hmoverObserver : mover ≠ observer)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (scale : ℝ) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1)
    (start : ℕ) (later : Option ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingNormalizedPureTimeGap reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              scale hscale0 hscale1)) observer start later -
        quittingNormalizedPureTimeGap reward
          (Function.update profile mover source) observer start later| ≤
      4 * bound * scale *
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start := by
  have hsharp :=
    abs_quittingNormalizedPureTimeGap_update_stoppingLawMixture_sub_le
      reward profile mover observer hmoverObserver source target scale
        hscale0 hscale1 start later bound hbound hreward
  have hsourceTail := quittingHazardSurvival_le_one
    (quittingBehaviorLiveHazard reward source) start
  have htargetTail := quittingHazardSurvival_le_one
    (quittingBehaviorLiveHazard reward target) start
  rw [stoppingLawSurvival_quittingBehaviorStoppingLaw,
    stoppingLawSurvival_quittingBehaviorStoppingLaw] at hsharp
  have hcoefficient : 0 ≤ 2 * bound * scale *
      quittingPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward profile) mover observer 0 start := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hbound) hscale0)
      (quittingPairDeletedSurvivalWeight_nonneg _ _ _ _ _)
  calc
    _ ≤ 2 * bound * scale *
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start *
        (quittingHazardSurvival
            (quittingBehaviorLiveHazard reward source) start +
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward target) start) := hsharp
    _ ≤ 2 * bound * scale *
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward profile) mover observer 0 start * 2 := by
          gcongr
          linarith
    _ = _ := by ring

end GameTheory
