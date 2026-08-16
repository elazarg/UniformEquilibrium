/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteCapClock
import UniformEquilibrium.Quitting.RewardBound

/-!
# One-coordinate finite-cap approximation

This module turns vanishing finite-splice error into simultaneous control of
prescribed payoff, behavioral best-response value, and terminal semantic debt.
It exposes finite caps with an arbitrary lower bound so callers can preserve a
requested live-path prefix.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-! ## One finite cutoff controls the whole terminal semantic port -/

/-- If the explicit splice error tends to zero, then at every requested
positive accuracy one finite cap simultaneously approximates every player's
prescribed payoff, unrestricted behavioral envelope, and semantic debt. -/
theorem exists_finiteCap_all_terminalSemantics_close_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (herror : Tendsto (fun cutoff =>
      quittingFiniteSpliceError (quittingProfileLiveRoot reward profile)
      mover (quittingBehaviorLiveHazard reward strategy) cutoff)
      atTop (nhds 0))
    (lowerBound : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  obtain ⟨M, hM, hreward⟩ :=
    exists_quittingRewardBound reward
  let error : ℕ → ℝ := fun cutoff =>
    quittingFiniteSpliceError (quittingProfileLiveRoot reward profile)
      mover (quittingBehaviorLiveHazard reward strategy) cutoff
  have hscaled : Tendsto (fun cutoff => 4 * M * error cutoff)
      atTop (nhds 0) := by
    have := herror.const_mul (4 * M)
    simpa [error] using this
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hscaled) δ hδ
  let cutoff := max lowerBound threshold
  have hlowerBound : lowerBound ≤ cutoff := le_max_left _ _
  have hthresholdCutoff : threshold ≤ cutoff := le_max_right _ _
  have herror0 : 0 ≤ error cutoff := by
    exact quittingFiniteSpliceError_nonneg
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) cutoff
  have hfourNonneg : 0 ≤ 4 * M * error cutoff := by positivity
  have hfour : 4 * M * error cutoff < δ := by
    have hclose := hthreshold cutoff hthresholdCutoff
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hfourNonneg] at hclose
    exact hclose
  have htwoLe : 2 * M * error cutoff ≤ 4 * M * error cutoff := by
    nlinarith [mul_nonneg hM herror0]
  refine ⟨cutoff, hlowerBound, fun observer => ?_⟩
  have hpay := abs_quittingTerminalPayoff_finiteCap_sub_le
    reward profile mover observer strategy cutoff hreward
  have hbest := abs_quittingContinuationBestResponseValue_finiteCap_sub_le
    reward profile mover observer strategy cutoff hreward
  have hdebt := abs_quittingTerminalSemanticDebt_finiteCap_sub_le
    reward profile mover observer strategy cutoff hreward
  dsimp only [error] at hfour htwoLe
  exact ⟨lt_of_le_of_lt hpay (lt_of_le_of_lt htwoLe hfour),
    lt_of_le_of_lt hbest (lt_of_le_of_lt htwoLe hfour),
    lt_of_le_of_lt hdebt hfour⟩

omit [Nontrivial ι] in
private theorem abs_quittingTerminalPayoff_finiteCap_sub_le_of_neverMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward strategy) = 0) :
    |quittingTerminalPayoff reward
          (Function.update profile mover strategy) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) observer| ≤
      2 * M * quittingHazardLateFiniteMass
        (quittingBehaviorLiveHazard reward strategy) cutoff := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_finiteCap]
  simpa [hnever] using
    (abs_quittingRootSequenceTerminalValue_finiteCap_sub_le_opponent
      reward (quittingProfileLiveRoot reward profile) mover observer
        (quittingBehaviorLiveHazard reward strategy) cutoff hreward)

omit [Nontrivial ι] in
private theorem
    abs_quittingContinuationBestResponseValue_finiteCap_sub_le_of_neverMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward strategy) = 0) :
    |quittingContinuationBestResponseValue reward
          (Function.update profile mover strategy) observer -
        quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
              cutoff)) observer| ≤
      2 * M * quittingHazardLateFiniteMass
        (quittingBehaviorLiveHazard reward strategy) cutoff := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward mover hreward
  by_cases hsame : mover = observer
  · subst observer
    rw [quittingContinuationBestResponseValue_update_self,
      quittingContinuationBestResponseValue_update_self, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hM)
      (quittingHazardLateFiniteMass_nonneg
        (quittingBehaviorLiveHazard reward strategy) cutoff)
  · letI : Nontrivial ι := nontrivial_of_ne mover observer hsame
    simpa [quittingFiniteSpliceError, hnever] using
      (abs_quittingContinuationBestResponseValue_finiteCap_sub_le
        reward profile mover observer strategy cutoff hreward)

omit [Nontrivial ι] in
private theorem
    abs_quittingTerminalSemanticDebt_finiteCap_sub_le_of_neverMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (strategy : (quittingGame reward).BehaviorStrategy mover)
    (cutoff : ℕ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward strategy) = 0) :
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover strategy)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff))) observer| ≤
      4 * M * quittingHazardLateFiniteMass
        (quittingBehaviorLiveHazard reward strategy) cutoff := by
  let source := Function.update profile mover strategy
  let capped := Function.update profile mover
    (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy cutoff)
  have hbest :=
    abs_quittingContinuationBestResponseValue_finiteCap_sub_le_of_neverMass_zero
      reward profile mover observer strategy cutoff hreward hnever
  have hpay :=
    abs_quittingTerminalPayoff_finiteCap_sub_le_of_neverMass_zero
      reward profile mover observer strategy cutoff hreward hnever
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change |(quittingContinuationBestResponseValue reward source observer -
      quittingTerminalPayoff reward source observer) -
    (quittingContinuationBestResponseValue reward capped observer -
      quittingTerminalPayoff reward capped observer)| ≤ _
  calc
    _ = |(quittingContinuationBestResponseValue reward source observer -
          quittingContinuationBestResponseValue reward capped observer) +
        (quittingTerminalPayoff reward capped observer -
          quittingTerminalPayoff reward source observer)| := by
      congr 1
      ring
    _ ≤ |quittingContinuationBestResponseValue reward source observer -
          quittingContinuationBestResponseValue reward capped observer| +
        |quittingTerminalPayoff reward capped observer -
          quittingTerminalPayoff reward source observer| := abs_add_le _ _
    _ = |quittingContinuationBestResponseValue reward source observer -
          quittingContinuationBestResponseValue reward capped observer| +
        |quittingTerminalPayoff reward source observer -
          quittingTerminalPayoff reward capped observer| := by
      exact congrArg
        (fun value =>
          |quittingContinuationBestResponseValue reward source observer -
              quittingContinuationBestResponseValue reward capped observer| + value)
        (abs_sub_comm
          (quittingTerminalPayoff reward capped observer)
          (quittingTerminalPayoff reward source observer))
    _ ≤ 2 * M * quittingHazardLateFiniteMass
          (quittingBehaviorLiveHazard reward strategy) cutoff +
        2 * M * quittingHazardLateFiniteMass
          (quittingBehaviorLiveHazard reward strategy) cutoff := by
      simpa only [source, capped] using add_le_add hbest hpay
    _ = 4 * M * quittingHazardLateFiniteMass
          (quittingBehaviorLiveHazard reward strategy) cutoff := by ring

omit [Nontrivial ι] in
/-- Finite-iteration reduction for a stochastic button with no `Never` atom. -/
theorem exists_finiteCap_all_terminalSemantics_close_of_neverMass_zero_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward strategy) = 0)
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  obtain ⟨M, hM, hreward⟩ := exists_quittingRewardBound reward
  let error : ℕ → ℝ := fun cutoff =>
    quittingHazardLateFiniteMass
      (quittingBehaviorLiveHazard reward strategy) cutoff
  have hscaled : Tendsto (fun cutoff => 4 * M * error cutoff)
      atTop (nhds 0) := by
    have := (tendsto_quittingHazardLateFiniteMass_zero
      (quittingBehaviorLiveHazard reward strategy)).const_mul (4 * M)
    simpa [error] using this
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hscaled) δ hδ
  let cutoff := max lowerBound threshold
  have hlowerBound : lowerBound ≤ cutoff := le_max_left _ _
  have hthresholdCutoff : threshold ≤ cutoff := le_max_right _ _
  have herror0 : 0 ≤ error cutoff := by
    exact quittingHazardLateFiniteMass_nonneg
      (quittingBehaviorLiveHazard reward strategy) cutoff
  have hfourNonneg : 0 ≤ 4 * M * error cutoff := by positivity
  have hfour : 4 * M * error cutoff < δ := by
    have hclose := hthreshold cutoff hthresholdCutoff
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hfourNonneg] at hclose
    exact hclose
  have htwoLe : 2 * M * error cutoff ≤ 4 * M * error cutoff := by
    nlinarith [mul_nonneg hM herror0]
  refine ⟨cutoff, hlowerBound, fun observer => ?_⟩
  have hpay :=
    abs_quittingTerminalPayoff_finiteCap_sub_le_of_neverMass_zero
      reward profile mover observer strategy cutoff hreward hnever
  have hbest :=
    abs_quittingContinuationBestResponseValue_finiteCap_sub_le_of_neverMass_zero
      reward profile mover observer strategy cutoff hreward hnever
  have hdebt :=
    abs_quittingTerminalSemanticDebt_finiteCap_sub_le_of_neverMass_zero
      reward profile mover observer strategy cutoff hreward hnever
  dsimp only [error] at hfour htwoLe
  exact ⟨lt_of_le_of_lt hpay (lt_of_le_of_lt htwoLe hfour),
    lt_of_le_of_lt hbest (lt_of_le_of_lt htwoLe hfour),
    lt_of_le_of_lt hdebt hfour⟩

/-- Finite-iteration reduction with a possible `Never` atom when every
relevant pair-deleted survival clock dies uniformly through their finite
maximum. -/
theorem exists_finiteCap_all_terminalSemantics_close_of_pairDeleted_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    (hclock : Tendsto (fun cutoff =>
      quittingMaxPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward profile) mover 0 cutoff)
      atTop (nhds 0))
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  apply exists_finiteCap_all_terminalSemantics_close_after
    reward profile mover strategy
  · exact tendsto_quittingFiniteSpliceError_zero_of_pairDeleted
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) hclock
  · exact hδ

/-! ## One-coordinate profile capping -/

/-- Cap the strategy currently assigned to one player inside a profile. -/
def quittingFiniteCapProfileAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (cutoff : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update profile mover
    (quittingStoppingLawFiniteCapBehaviorStrategy reward mover
      (profile mover) cutoff)

omit [Nontrivial ι] in
/-- The no-Never one-button theorem in profile-to-profile form. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile mover)) = 0)
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |(quittingTerminalSemanticPair reward profile).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward profile).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward profile mover cutoff))
              observer| < δ := by
  obtain ⟨cutoff, hlower, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_neverMass_zero_after
      reward profile mover (profile mover) hnever lowerBound hδ
  refine ⟨cutoff, hlower, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

omit [Nontrivial ι] in
/-- Two distinct zero-Never opponents make an arbitrary mover directly
cappable, even if the mover itself has positive Never mass.  This version
uses their decaying survival curves and does not first replace them by
sure-Quit sentinels. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_two_zeroNeverOpponents_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (hneverFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0)
    (lowerBound : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |(quittingTerminalSemanticPair reward profile).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward profile).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward profile mover cutoff))
              observer| < δ := by
  letI : Nontrivial ι := nontrivial_of_ne first second hfirstSecond
  have hneverFirstRoot : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard
        (quittingProfileLiveRoot reward profile) first) = 0 := by
    change quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0
    exact hneverFirst
  have hneverSecondRoot : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard
        (quittingProfileLiveRoot reward profile) second) = 0 := by
    change quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0
    exact hneverSecond
  obtain ⟨cutoff, hlower, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_pairDeleted_after
      reward profile mover (profile mover)
      (tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
        (quittingProfileLiveRoot reward profile) mover first second
          hfirstSecond hfirstMover hsecondMover hneverFirstRoot
          hneverSecondRoot)
      lowerBound hδ
  refine ⟨cutoff, hlower, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

end GameTheory
