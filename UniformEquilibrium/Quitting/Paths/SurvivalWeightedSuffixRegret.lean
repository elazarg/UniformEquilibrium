/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Optimization.SupremumTwoResetWitnessSwitch
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding

/-!
# Survival-weighted suffix regret

This file proves the exact transport of a pure-time deviation comparison
from a quitting source to a reached suffix.  A suffix choice is a relative
delay, so it is first rebased to an absolute source date.  Prefix scaling
then gives the source difference as opponent survival to the suffix times
the reached-suffix difference.  The corresponding supremum-envelope
inequality does not assume that either supremum is attained.

The same file gives a thin adapter from actual quitting pure-time values to
the generic four-corner supremum witness-switch lemmas.  It does not assert
that a radial reset cube supplies a common passport or chronological renewal
construction.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Absolute pure-time stops and their caps -/

/-- Turn a quit time measured from a reached suffix into its absolute source
time.  `Never` remains `Never`. -/
def quittingAbsolutePureTime (start : ℕ) : Option ℕ → Option ℕ
  | none => none
  | some delay => some (start + delay)

@[simp] theorem quittingAbsolutePureTime_zero (quitTime : Option ℕ) :
    quittingAbsolutePureTime 0 quitTime = quitTime := by
  cases quitTime <;> simp [quittingAbsolutePureTime]

/-- The value from a reached suffix of a quit delay measured relative to the
suffix.  Evaluation uses the same absolute root sequence as the source. -/
def quittingRootSequenceRelativePureTimeTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (delay : Option ℕ) : ℝ :=
  quittingRootSequencePureTimeTerminalValue reward roots who
    (quittingAbsolutePureTime start delay) start

/-- The relative pure-time best-response envelope at a reached live date. -/
def quittingPureTimeBestResponseCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) : ℝ :=
  sSup (Set.range
    (quittingRootSequenceRelativePureTimeTerminalValue reward roots who start))

/-- The pure-time values are bounded above at every live date by the standard
terminal reward bound. -/
theorem bddAbove_range_quittingRootSequencePureTimeTerminalValue_at
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    BddAbove (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime start) := by
  refine ⟨quittingRewardBound reward, ?_⟩
  rintro value ⟨quitTime, rfl⟩
  exact (le_abs_self _).trans (by
    simpa [quittingRootSequencePureTimeTerminalValue,
      quittingRootSequenceHazardTerminalValue,
      quittingRootSequenceTerminalValue] using
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward
        (quittingRootSequenceProfile reward
          (quittingRootSequenceUpdate roots who
            (quittingPureTimeHazard quitTime)) start)
        who))

/-- The relative pure-time payoff set at a reached date is bounded above. -/
theorem bddAbove_range_quittingRootSequenceRelativePureTimeTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    BddAbove (Set.range
      (quittingRootSequenceRelativePureTimeTerminalValue reward roots who start)) := by
  obtain ⟨bound, hbound⟩ :=
    bddAbove_range_quittingRootSequencePureTimeTerminalValue_at
      reward roots who start
  refine ⟨bound, ?_⟩
  rintro value ⟨delay, rfl⟩
  exact hbound ⟨quittingAbsolutePureTime start delay, rfl⟩

/-- Before the reached date, every rebased pure-time deviation continues
surely. -/
theorem quittingPureTimeHazard_absolute_eq_continue_of_lt
    (start : ℕ) (delay : Option ℕ) {time : ℕ} (htime : time < start) :
    quittingPureTimeHazard (quittingAbsolutePureTime start delay) time =
      PMF.pure false := by
  cases delay with
  | none => rfl
  | some delay =>
      apply quittingPureTimeHazard_some_of_ne
      omega

/-- Exact source-to-suffix transport for two relative pure-time choices.
Both suffix choices are rebased to absolute source dates before evaluation.
The deviator surely continues through the common prefix, so joint survival
of either deviated sequence there is exactly the opponents' survival. -/
theorem quittingRelativePureTimeTerminalValue_sub_prefixTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (first second : Option ℕ) :
    quittingOpponentSurvivalWeight roots who 0 start *
        (quittingRootSequenceRelativePureTimeTerminalValue
            reward roots who start first -
          quittingRootSequenceRelativePureTimeTerminalValue
            reward roots who start second) =
      quittingRootSequencePureTimeTerminalValue reward roots who
          (quittingAbsolutePureTime start first) 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (quittingAbsolutePureTime start second) 0 := by
  let firstRoots := quittingRootSequenceUpdate roots who
    (quittingPureTimeHazard (quittingAbsolutePureTime start first))
  let secondRoots := quittingRootSequenceUpdate roots who
    (quittingPureTimeHazard (quittingAbsolutePureTime start second))
  have hagree : ∀ time, time < start → firstRoots time = secondRoots time := by
    intro time htime
    unfold firstRoots secondRoots quittingRootSequenceUpdate
    rw [quittingPureTimeHazard_absolute_eq_continue_of_lt start first htime,
      quittingPureTimeHazard_absolute_eq_continue_of_lt start second htime]
  have hprefix :=
    quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul
      reward firstRoots secondRoots who start hagree
  have hsurvival : quittingJointSurvivalWeight secondRoots 0 start =
      quittingOpponentSurvivalWeight roots who 0 start := by
    rw [quittingJointSurvivalWeight_eq_prod]
    unfold quittingOpponentSurvivalWeight
    apply Finset.prod_congr rfl
    intro offset hoffset
    have hlt : offset < start := Finset.mem_range.mp hoffset
    rw [Nat.zero_add]
    unfold secondRoots quittingRootSequenceUpdate
    rw [quittingPureTimeHazard_absolute_eq_continue_of_lt start second hlt]
    rfl
  rw [hsurvival] at hprefix
  symm
  simpa [quittingRootSequenceRelativePureTimeTerminalValue,
    quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue, firstRoots, secondRoots] using hprefix

/-- **Exact first-disagreement decoder.** If one pure plan quits at the
reached date and the other uses a delay measured from that date (including
`Never`), their source payoff difference is opponent survival to the date
times immediate-Quit payoff minus the delayed plan's reached-suffix payoff.

For a positive finite delay this is the literal first date at which the two
plans differ. No best-response attainment or positivity assumption is used. -/
theorem quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (later : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
          (some start) 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (quittingAbsolutePureTime start later) 0 =
      quittingOpponentSurvivalWeight roots who 0 start *
        (quittingFixedOpponentsQuitValue reward roots who start -
          quittingRootSequenceRelativePureTimeTerminalValue
            reward roots who start later) := by
  have htransport :=
    quittingRelativePureTimeTerminalValue_sub_prefixTransport
      reward roots who start (some 0) later
  simp only [quittingRootSequenceRelativePureTimeTerminalValue,
    quittingAbsolutePureTime, Nat.add_zero] at htransport
  rw [
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
    at htransport
  simpa [quittingRootSequenceRelativePureTimeTerminalValue,
    quittingAbsolutePureTime] using htransport.symm

/-- Absolute-date specialization of the first-disagreement decoder for two
finite quit times. -/
theorem quittingPureTimeEarlierValue_sub_later_eq_opponentSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (earlier later : ℕ)
    (hle : earlier ≤ later) :
    quittingRootSequencePureTimeTerminalValue reward roots who
          (some earlier) 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (some later) 0 =
      quittingOpponentSurvivalWeight roots who 0 earlier *
        (quittingFixedOpponentsQuitValue reward roots who earlier -
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some later) earlier) := by
  have hmain :=
    quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
      reward roots who earlier (some (later - earlier))
  simpa [quittingRootSequenceRelativePureTimeTerminalValue,
    quittingAbsolutePureTime, Nat.add_sub_of_le hle] using hmain

/-! ## The unconditional suffix regret inequality -/

/-- A source passport's reached-suffix regret, weighted by opponent survival
to that suffix, is bounded by its source regret.  The suffix stopping times
are relative delays rebased to absolute source dates.  Both caps are explicit
`sSup`s, and boundedness is discharged by the canonical terminal bound, so
no best-response attainment or extra transport premise is assumed. -/
theorem quittingPureTimeSuffixRegret_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (passport : Option ℕ) :
    quittingOpponentSurvivalWeight roots who 0 start *
        (quittingPureTimeBestResponseCap reward roots who start -
          quittingRootSequenceRelativePureTimeTerminalValue
            reward roots who start passport) ≤
      quittingPureTimeBestResponseCap reward roots who 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (quittingAbsolutePureTime start passport) 0 := by
  let survival := quittingOpponentSurvivalWeight roots who 0 start
  let suffixValue : Option ℕ → ℝ := fun quitTime ↦
    quittingRootSequenceRelativePureTimeTerminalValue
      reward roots who start quitTime
  let sourceValue : Option ℕ → ℝ := fun quitTime ↦
    quittingRootSequencePureTimeTerminalValue reward roots who
      (quittingAbsolutePureTime start quitTime) 0
  let suffixCap : ℝ := sSup (Set.range suffixValue)
  let sourceCap : ℝ := quittingPureTimeBestResponseCap reward roots who 0
  have hsurvival : 0 ≤ survival := by
    exact quittingOpponentSurvivalWeight_nonneg roots who 0 start
  have hsurvival_le_one : survival ≤ 1 := by
    exact quittingOpponentSurvivalWeight_le_one roots who 0 start
  have htransport' : ∀ first second,
      survival * (suffixValue first - suffixValue second) =
        sourceValue first - sourceValue second := by
    intro first second
    exact quittingRelativePureTimeTerminalValue_sub_prefixTransport
      reward roots who start first second
  have hsuffix : BddAbove (Set.range suffixValue) := by
    exact bddAbove_range_quittingRootSequenceRelativePureTimeTerminalValue
      reward roots who start
  have hsource : BddAbove (Set.range fun quitTime : Option ℕ =>
      quittingRootSequenceRelativePureTimeTerminalValue
        reward roots who 0 quitTime) := by
    exact bddAbove_range_quittingRootSequenceRelativePureTimeTerminalValue
      reward roots who 0
  have hsuffixNonempty : (Set.range suffixValue).Nonempty := by
    exact ⟨suffixValue none, ⟨none, rfl⟩⟩
  have hsourceValue_le : ∀ quitTime, sourceValue quitTime ≤ sourceCap := by
    intro quitTime
    dsimp [sourceValue, sourceCap]
    apply le_csSup hsource
    refine ⟨quittingAbsolutePureTime start quitTime, ?_⟩
    simp [quittingRootSequenceRelativePureTimeTerminalValue]
  have hscaled : ∀ ε : ℝ, 0 < ε →
      survival * (suffixCap - suffixValue passport) ≤
        sourceCap - sourceValue passport + ε := by
    intro ε hε
    have hlt : suffixCap - ε < suffixCap := sub_lt_self _ hε
    obtain ⟨value, ⟨quitTime, rfl⟩, hnear⟩ :=
      (lt_csSup_iff hsuffix hsuffixNonempty).mp hlt
    have hnear' : suffixCap - ε < suffixValue quitTime := by
      simpa [suffixValue] using hnear
    have hsourceNear : sourceValue quitTime - sourceValue passport ≤
        sourceCap - sourceValue passport := by
      linarith [hsourceValue_le quitTime]
    have htransportValue := htransport' quitTime passport
    have hpoint : survival * (suffixValue quitTime - suffixValue passport) ≤
        sourceCap - sourceValue passport := by
      rw [htransportValue]
      exact hsourceNear
    have hscaledNear : survival * (suffixCap - ε - suffixValue passport) ≤
        sourceCap - sourceValue passport := by
      have hsurvivalScaled := mul_le_mul_of_nonneg_left hnear.le hsurvival
      calc
        survival * (suffixCap - ε - suffixValue passport) =
            survival * (suffixCap - ε) - survival * suffixValue passport := by ring
        _ ≤ survival * suffixValue quitTime - survival * suffixValue passport := by
          exact sub_le_sub_right hsurvivalScaled _
        _ = survival * (suffixValue quitTime - suffixValue passport) := by ring
        _ ≤ sourceCap - sourceValue passport := hpoint
    have hεscaled : survival * ε ≤ ε := by
      nlinarith
    calc
      survival * (suffixCap - suffixValue passport) =
          survival * (suffixCap - ε - suffixValue passport) + survival * ε := by
        ring
      _ ≤ sourceCap - sourceValue passport + ε := by
        exact add_le_add hscaledNear hεscaled
  dsimp [quittingPureTimeBestResponseCap, suffixCap, sourceCap,
    suffixValue, sourceValue] at hscaled ⊢
  exact le_of_forall_pos_le_add (fun ε hε => hscaled ε hε)

/-- Absolute-date form of the suffix regret inequality.  The finite source
passport `quitTime` is converted to the relative suffix delay
`quitTime - start` only through the explicit rebasing definition. -/
theorem quittingPureTimeSuffixRegret_le_at_absoluteQuitTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start quitTime : ℕ)
    (hstart : start ≤ quitTime) :
    quittingOpponentSurvivalWeight roots who 0 start *
        (quittingPureTimeBestResponseCap reward roots who start -
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some quitTime) start) ≤
      quittingPureTimeBestResponseCap reward roots who 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (some quitTime) 0 := by
  have hmain := quittingPureTimeSuffixRegret_le
    reward roots who start (some (quitTime - start))
  simpa [quittingRootSequenceRelativePureTimeTerminalValue,
    quittingAbsolutePureTime, Nat.add_sub_of_le hstart] using hmain

/-! ## Adapter to the pure-time witness-switch interface -/

/-- A four-corner face value obtained from an actual quitting root sequence.
The face index is intentionally abstract: this adapter does not identify a
chronological carrier for the four corners. -/
def quittingPureTimeFaceValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {κ : Type*} (faces : κ → ℕ → ι → PMF Bool) (face : κ)
    (who : ι) (quitTime : Option ℕ) : ℝ :=
  quittingRootSequencePureTimeTerminalValue reward (faces face) who quitTime 0

/-- The generic upper-to-base witness-switch bound, instantiated with actual
quitting pure-time values on four faces. -/
theorem quittingPureTimeFace_upperToBase_regret_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {κ : Type*} (faces : κ → ℕ → ι → PMF Bool)
    (base one two both : κ) (who : ι)
    (q eta : ℝ) (quitTime : Option ℕ)
    (hface : ∀ choice : Option ℕ,
      |quittingPureTimeFaceValue reward faces both who choice -
          quittingPureTimeFaceValue reward faces one who choice -
          quittingPureTimeFaceValue reward faces two who choice +
          quittingPureTimeFaceValue reward faces base who choice| ≤ q)
    (hupper : sSup (Set.range (quittingPureTimeFaceValue reward faces both who)) -
      eta ≤ quittingPureTimeFaceValue reward faces both who quitTime) :
    Math.Optimization.supMixedDifference
        (quittingPureTimeFaceValue reward faces base who)
        (quittingPureTimeFaceValue reward faces one who)
        (quittingPureTimeFaceValue reward faces two who)
        (quittingPureTimeFaceValue reward faces both who) - (q + eta) ≤
      Math.Optimization.baseRegret
        (quittingPureTimeFaceValue reward faces base who) quitTime := by
  have h₁ : BddAbove
      (Set.range (quittingPureTimeFaceValue reward faces one who)) := by
    change BddAbove (Set.range fun choice : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward (faces one) who choice 0)
    exact bddAbove_range_quittingRootSequencePureTimeTerminalValue_at
      reward (faces one) who 0
  have h₂ : BddAbove
      (Set.range (quittingPureTimeFaceValue reward faces two who)) := by
    change BddAbove (Set.range fun choice : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward (faces two) who choice 0)
    exact bddAbove_range_quittingRootSequencePureTimeTerminalValue_at
      reward (faces two) who 0
  exact Math.Optimization.upperToBase_regret_ge_supMixedDifference_sub
    (quittingPureTimeFaceValue reward faces base who)
    (quittingPureTimeFaceValue reward faces one who)
    (quittingPureTimeFaceValue reward faces two who)
    (quittingPureTimeFaceValue reward faces both who)
    h₁ h₂ q eta quitTime hface hupper

end GameTheory
