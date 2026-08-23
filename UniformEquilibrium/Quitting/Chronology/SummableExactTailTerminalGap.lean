/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Classification.Existence.QuietWindowStationaryRepair
import UniformEquilibrium.Quitting.Terminal.TailCompression.SummableTailBestResponse
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection
import MathUE.Topology.TailSupConvergence

/-!
# Terminal semantics of a summable exact quitting tail

An exact Bellman value path may converge to a nonzero phantom boundary even
though executing late suffixes delivers payoff zero.  When the unweighted
one-row absorption masses are summable, the unrestricted behavioral
best-response value of a late suffix converges instead to the positive part
of the player's singleton payoff.

This module packages only the source data: literal product roots, an exact
Bellman value path, its limit, and summable joint absorption.  All terminal
identities and strategic conclusions are derived.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A convergent exact Bellman path with finite total joint absorption.
No Nash or punishment assumption is needed for its terminal semantics. -/
structure QuittingSummableExactValueTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  boundary : Payoff ι
  bellman : ∀ time,
    value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)
  value_tendsto : ∀ who,
    Tendsto (fun time ↦ value time who) atTop (nhds (boundary who))
  absorption_summable :
    Summable (fun time ↦ quittingRootAbsorptionMass (roots time))

namespace QuittingSummableExactValueTail

variable (tail : QuittingSummableExactValueTail reward)

/-- The literal executable profile starting at a tail date. -/
def suffixProfile (start : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward tail.roots start

/-- Remaining unweighted joint absorption charge. -/
def remainingCharge (start : ℕ) : ℝ :=
  ∑' offset : ℕ, quittingRootAbsorptionMass (tail.roots (start + offset))

/-- Unrestricted behavioral best-response envelope against a suffix. -/
def suffixBestResponseValue (start : ℕ) (who : ι) : ℝ :=
  quittingContinuationBestResponseValue reward (tail.suffixProfile start) who

/-- Positive unrestricted unilateral gain against a suffix. -/
def suffixGain (start : ℕ) (who : ι) : ℝ :=
  max 0 (tail.suffixBestResponseValue start who -
    quittingTerminalPayoff reward (tail.suffixProfile start) who)

/-- Payoff at one tail row when `who` is forced to Quit while all opponents
retain their displayed marginals. -/
def forcedQuitValue (time : ℕ) (who : ι) : ℝ :=
  quittingRootExpectedPayoff reward (tail.value (time + 1))
    (Function.update (tail.roots time) who (PMF.pure true)) who

/-- The best one-row forced-Quit payoff available on a displayed suffix. -/
def forcedQuitTailSup (start : ℕ) (who : ι) : ℝ :=
  sSup (Set.range fun offset ↦ tail.forcedQuitValue (start + offset) who)

/-- Largest coordinatewise unrestricted gain of one suffix. -/
def maxSuffixGain [Nonempty ι] (start : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who ↦ tail.suffixGain start who

omit [DecidableEq ι] in
private theorem remainingCharge_tendsto_zero :
    Tendsto tail.remainingCharge atTop (nhds 0) := by
  have hprefix := tail.absorption_summable.hasSum.tendsto_sum_nat
  have htail : ∀ start,
      tail.remainingCharge start =
        (∑' time : ℕ, quittingRootAbsorptionMass (tail.roots time)) -
          ∑ time ∈ Finset.range start,
            quittingRootAbsorptionMass (tail.roots time) := by
    intro start
    have hsplit := tail.absorption_summable.sum_add_tsum_nat_add start
    rw [← hsplit]
    simp only [remainingCharge, Nat.add_comm]
    ring
  rw [show tail.remainingCharge = fun start ↦
      (∑' time : ℕ, quittingRootAbsorptionMass (tail.roots time)) -
        ∑ time ∈ Finset.range start,
          quittingRootAbsorptionMass (tail.roots time) by
    funext start
    exact htail start]
  simpa only [sub_self] using
    ((tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ ∑' time : ℕ,
        quittingRootAbsorptionMass (tail.roots time)) atTop
        (nhds (∑' time : ℕ,
          quittingRootAbsorptionMass (tail.roots time)))).sub hprefix)

omit [DecidableEq ι] in
/-- Every shifted absorption series remains summable. -/
theorem summable_shifted_absorption (start : ℕ) :
    Summable (fun offset ↦
      quittingRootAbsorptionMass (tail.roots (start + offset))) := by
  have hinjective : Function.Injective (fun offset : ℕ ↦ start + offset) := by
    intro first second heq
    exact Nat.add_left_cancel heq
  exact tail.absorption_summable.comp_injective hinjective

omit [DecidableEq ι] in
/-- Exact phantom-boundary identity for every literal suffix. -/
theorem value_eq_terminalPayoff_add_survival_mul_boundary (start : ℕ) :
    tail.value start = fun who ↦
      quittingTerminalPayoff reward (tail.suffixProfile start) who +
        quittingJointSurvivalLimit tail.roots start * tail.boundary who := by
  simpa only [suffixProfile, quittingRootSequenceTerminalValue] using
    quittingValuePath_eq_terminalValue_add_survivalLimit_mul
      reward tail.roots tail.value tail.bellman tail.boundary
        tail.value_tendsto start

omit [DecidableEq ι] in
/-- Joint survival of later suffixes tends to one. -/
theorem jointSurvivalLimit_tendsto_one :
    Tendsto (fun start ↦ quittingJointSurvivalLimit tail.roots start)
      atTop (nhds 1) := by
  have hgap : Tendsto
      (fun start ↦ 1 - quittingJointSurvivalLimit tail.roots start)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro start
      exact sub_nonneg.mpr <| le_of_tendsto'
        (tendsto_quittingJointSurvivalLimit tail.roots start)
        (fun fuel ↦ quittingJointSurvivalWeight_le_one tail.roots start fuel)
    · intro start
      exact one_sub_quittingJointSurvivalLimit_le_tailCharge
        tail.roots start (tail.summable_shifted_absorption start)
    · exact tail.remainingCharge_tendsto_zero
  have hreconstruct :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub hgap
  simpa using hreconstruct

omit [DecidableEq ι] in
/-- Executing later suffixes delivers payoff zero. -/
theorem terminalPayoff_tendsto_zero (who : ι) :
    Tendsto (fun start ↦
      quittingTerminalPayoff reward (tail.suffixProfile start) who)
      atTop (nhds 0) := by
  have hbound : ∀ start,
      |quittingTerminalPayoff reward (tail.suffixProfile start) who| ≤
        quittingRewardBound reward * tail.remainingCharge start := by
    intro start
    simpa only [suffixProfile, quittingRootSequenceTerminalValue,
      remainingCharge] using
      abs_quittingRootSequenceTerminalValue_le_tailCharge
        reward tail.roots who start
          (abs_reward_le_quittingRewardBound reward)
          (tail.summable_shifted_absorption start)
  refine squeeze_zero_norm (a := fun start ↦
    quittingRewardBound reward * tail.remainingCharge start) ?_ ?_
  · intro start
    simpa [Real.norm_eq_abs] using hbound start
  · simpa using tail.remainingCharge_tendsto_zero.const_mul
      (quittingRewardBound reward)

/-- Forced Quit at a later row converges to the player's literal singleton
payoff, uniformly in the displayed continuation annotation. -/
theorem forcedQuitValue_tendsto_solo (who : ι) :
    Tendsto (fun time ↦ tail.forcedQuitValue time who) atTop
      (nhds (reward (quittingSingletonTerminal who) who)) := by
  have habsorption : Tendsto
      (fun time ↦ quittingRootAbsorptionMass (tail.roots time))
      atTop (nhds 0) := tail.absorption_summable.tendsto_atTop_zero
  have hopponent : Tendsto
      (fun time ↦ quittingRootOpponentAbsorptionMass (tail.roots time) who)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro time
      exact quittingRootOpponentAbsorptionMass_nonneg _ _
    · intro time
      exact quittingRootOpponentAbsorptionMass_le_absorptionMass _ _
    · exact habsorption
  have hbound : ∀ time,
      |tail.forcedQuitValue time who -
          reward (quittingSingletonTerminal who) who| ≤
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (tail.roots time) who := by
    intro time
    simpa [forcedQuitValue, quittingSoloReward,
      quittingSingletonTerminal] using
      abs_quittingRootExpectedPayoff_forcedQuit_sub_soloReward_le
        reward (tail.value (time + 1)) (tail.roots time) who who
          (abs_reward_le_quittingRewardBound reward)
  have hzero : Tendsto (fun time ↦
      tail.forcedQuitValue time who -
        reward (quittingSingletonTerminal who) who) atTop (nhds 0) := by
    apply squeeze_zero_norm' (Filter.Eventually.of_forall fun time ↦ by
      simpa [Real.norm_eq_abs] using hbound time)
    simpa using hopponent.const_mul (2 * quittingRewardBound reward)
  have hrecover := hzero.add_const
    (reward (quittingSingletonTerminal who) who)
  simpa using hrecover

/-- The supremum of all later forced-Quit values converges to the literal
singleton payoff. -/
theorem forcedQuitTailSup_tendsto_solo (who : ι) :
    Tendsto (fun start ↦ tail.forcedQuitTailSup start who) atTop
      (nhds (reward (quittingSingletonTerminal who) who)) := by
  simpa only [forcedQuitTailSup] using
    Math.tendsto_csSup_range_natAdd_of_tendsto
      (tail.forcedQuitValue_tendsto_solo who)

/-- Quantitative unrestricted best-response modulus for one late suffix. -/
theorem abs_suffixBestResponseValue_sub_max_solo_le
    (start : ℕ) (who : ι) (hsmall : tail.remainingCharge start < 1) :
    |tail.suffixBestResponseValue start who -
        max 0 (reward (quittingSingletonTerminal who) who)| ≤
      2 * quittingRewardBound reward * tail.remainingCharge start := by
  let shifted : ℕ → ι → PMF Bool :=
    fun offset ↦ tail.roots (start + offset)
  have hsummable : Summable (fun offset ↦
      quittingRootAbsorptionMass (shifted offset)) := by
    simpa [shifted] using tail.summable_shifted_absorption start
  have hestimate :=
    abs_quittingRootSequenceBestResponseValue_sub_maxSolo_le_totalCharge_of_lt_one
      reward shifted who (abs_reward_le_quittingRewardBound reward)
        hsummable (by simpa [remainingCharge, shifted] using hsmall)
  simpa [suffixBestResponseValue, suffixProfile,
    quittingRootSequenceBestResponseValue,
    quittingRootSequenceProfile_eq_shift, remainingCharge, shifted] using
    hestimate

/-- The unrestricted best-response envelope of later suffixes converges to
the positive part of the player's literal singleton payoff. -/
theorem suffixBestResponseValue_tendsto_max_solo (who : ι) :
    Tendsto (fun start ↦ tail.suffixBestResponseValue start who) atTop
      (nhds (max 0 (reward (quittingSingletonTerminal who) who))) := by
  have hsmall : ∀ᶠ start in atTop, tail.remainingCharge start < 1 :=
    (tendsto_order.1 tail.remainingCharge_tendsto_zero).2 1 zero_lt_one
  have hbound : ∀ᶠ start in atTop,
      |tail.suffixBestResponseValue start who -
          max 0 (reward (quittingSingletonTerminal who) who)| ≤
        2 * quittingRewardBound reward * tail.remainingCharge start := by
    filter_upwards [hsmall] with start hstart
    exact tail.abs_suffixBestResponseValue_sub_max_solo_le start who hstart
  have hnorm : ∀ᶠ start in atTop,
      ‖tail.suffixBestResponseValue start who -
          max 0 (reward (quittingSingletonTerminal who) who)‖ ≤
        2 * quittingRewardBound reward * tail.remainingCharge start :=
    hbound.mono fun _ hstart ↦ by
      simpa [Real.norm_eq_abs] using hstart
  have hzero := squeeze_zero_norm' hnorm (by
    simpa using tail.remainingCharge_tendsto_zero.const_mul
      (2 * quittingRewardBound reward))
  have hrecover := hzero.add_const
    (max 0 (reward (quittingSingletonTerminal who) who))
  simpa using hrecover

/-- Coordinatewise unrestricted exploitability converges exactly to the
positive part of the player's singleton payoff. -/
theorem suffixGain_tendsto_max_solo (who : ι) :
    Tendsto (fun start ↦ tail.suffixGain start who) atTop
      (nhds (max 0 (reward (quittingSingletonTerminal who) who))) := by
  have hdiff := (tail.suffixBestResponseValue_tendsto_max_solo who).sub
    (tail.terminalPayoff_tendsto_zero who)
  have hmax :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0)).max
      hdiff
  simpa [suffixGain, max_self] using hmax

/-- Late unrestricted exploitability differs negligibly from the positive
part of the best forced-Quit value visible anywhere on the same suffix. -/
theorem suffixGain_sub_max_forcedQuitTailSup_tendsto_zero (who : ι) :
    Tendsto (fun start ↦ tail.suffixGain start who -
      max 0 (tail.forcedQuitTailSup start who)) atTop (nhds 0) := by
  have hgain := tail.suffixGain_tendsto_max_solo who
  have hforced :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0)).max
      (tail.forcedQuitTailSup_tendsto_solo who))
  simpa using hgain.sub hforced

/-- The largest unrestricted gain converges to the largest positive singleton
self-payoff. -/
theorem maxSuffixGain_tendsto_max_solo [Nonempty ι] :
    Tendsto tail.maxSuffixGain atTop (nhds
      (Finset.univ.sup' Finset.univ_nonempty fun who ↦
        max 0 (reward (quittingSingletonTerminal who) who))) := by
  exact Filter.Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
    (fun who _ ↦ tail.suffixGain_tendsto_max_solo who)

/-- With nonpositive singleton self-payoffs, a sufficiently late suffix is a
terminal Nash profile with error `3 M` times its remaining absorption charge. -/
theorem suffixProfile_isTerminalNash_of_nonpositive_solo
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤ 0)
    (start : ℕ) (hsmall : tail.remainingCharge start < 1) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (3 * quittingRewardBound reward * tail.remainingCharge start)
      (tail.suffixProfile start) := by
  intro who deviation
  have hbest : quittingTerminalPayoff reward
      (Function.update (tail.suffixProfile start) who deviation) who ≤
      tail.suffixBestResponseValue start who := by
    unfold suffixBestResponseValue quittingContinuationBestResponseValue
    exact le_csSup
      (bddAbove_range_quittingTerminalPayoff_update
        reward (tail.suffixProfile start) who)
      ⟨deviation, rfl⟩
  have hbestBound :=
    tail.abs_suffixBestResponseValue_sub_max_solo_le start who hsmall
  rw [max_eq_left (hsolo who)] at hbestBound
  simp only [sub_zero] at hbestBound
  have hterminalBound := abs_quittingRootSequenceTerminalValue_le_tailCharge
    reward tail.roots who start (abs_reward_le_quittingRewardBound reward)
      (tail.summable_shifted_absorption start)
  change quittingTerminalPayoff reward (tail.suffixProfile start) who +
      3 * quittingRewardBound reward * tail.remainingCharge start ≥ _
  have hcharge : 0 ≤ tail.remainingCharge start := by
    exact tsum_nonneg fun offset ↦ quittingRootAbsorptionMass_nonneg _
  have hM := quittingRewardBound_nonneg reward
  have hbestUpper : tail.suffixBestResponseValue start who ≤
      2 * quittingRewardBound reward * tail.remainingCharge start := by
    exact (le_abs_self _).trans hbestBound
  have hterminalLower :
      -(quittingRewardBound reward * tail.remainingCharge start) ≤
        quittingTerminalPayoff reward (tail.suffixProfile start) who := by
    simpa only [suffixProfile, quittingRootSequenceTerminalValue,
      remainingCharge] using
      neg_le_of_abs_le hterminalBound
  nlinarith

/-- Every nonpositive-solo summable exact value tail witnesses that zero is a
uniform-equilibrium payoff. -/
theorem zero_isUniformEquilibriumPayoff_of_nonpositive_solo
    [Nonempty ι]
    (tail : QuittingSummableExactValueTail reward)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤ 0) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι) := by
  let error : ℕ → ℝ := fun start ↦
    3 * quittingRewardBound reward * tail.remainingCharge start
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using tail.remainingCharge_tendsto_zero.const_mul
      (3 * quittingRewardBound reward)
  have hsmall : ∀ᶠ start in atTop, tail.remainingCharge start < 1 :=
    (tendsto_order.1 tail.remainingCharge_tendsto_zero).2 1 zero_lt_one
  have hnash : ∃ᶠ start in atTop,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (error start)
        (tail.suffixProfile start) :=
    (hsmall.mono fun start hstart ↦ by
      exact tail.suffixProfile_isTerminalNash_of_nonpositive_solo
        hsolo start hstart).frequently
  have htarget : Tendsto
      (fun start ↦ quittingTerminalPayoff reward (tail.suffixProfile start))
      atTop (nhds (0 : Payoff ι)) := by
    apply tendsto_pi_nhds.2
    intro who
    simpa using tail.terminalPayoff_tendsto_zero who
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward (0 : Payoff ι) error tail.suffixProfile herror hnash htarget

end QuittingSummableExactValueTail

end GameTheory
