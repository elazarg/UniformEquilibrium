/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Optimization.SupremumTwoResetWitnessSwitch
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing

/-!
# Survival-weighted suffix regret

This file records the exact interface needed to transport a pure-time
deviation comparison from a quitting source to a reached suffix.  The
transport is stated as a proposition rather than inferred from a terminal
cap: producing it is a chronological task.  Once supplied, the supremum
envelope inequality is an elementary consequence of nonnegative opponent
survival.

The same file gives a thin adapter from actual quitting pure-time values to
the generic four-corner supremum witness-switch lemmas.  It does not assert
that a radial reset cube supplies the transport or a common passport.
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

/-- The pure-time best-response envelope at a live date. -/
def quittingPureTimeBestResponseCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) : ℝ :=
  sSup (Set.range fun quitTime : Option ℕ =>
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime start)

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

/-- A source-to-suffix pure-time transport identity.  This is the exact
survival-weighted comparison behind a suffix passport: both deviations are
measured from the same reached date, and their source versions are obtained
by prefixing that date. -/
def IsQuittingPureTimePrefixTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) : Prop :=
  ∀ (start : ℕ) (first second : Option ℕ),
    quittingOpponentSurvivalWeight roots who 0 start *
        (quittingRootSequencePureTimeTerminalValue reward roots who first start -
          quittingRootSequencePureTimeTerminalValue reward roots who second start) =
      quittingRootSequencePureTimeTerminalValue reward roots who
          (quittingAbsolutePureTime start first) 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (quittingAbsolutePureTime start second) 0

/-! ## The suffix regret inequality -/

/-- Survival-weighted suffix regret is bounded by source regret whenever the
pure-time prefix transport identity is available.  The source and suffix
caps are explicit `sSup`s, so no best-response attainment is assumed. -/
theorem quittingPureTimeSuffixRegret_le_of_prefixTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (passport : Option ℕ)
    (htransport : IsQuittingPureTimePrefixTransport reward roots who)
    (hsource : BddAbove (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0))
    (hsuffix : BddAbove (Set.range fun quitTime : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime start)) :
    quittingOpponentSurvivalWeight roots who 0 start *
        (quittingPureTimeBestResponseCap reward roots who start -
          quittingRootSequencePureTimeTerminalValue reward roots who passport start) ≤
      quittingPureTimeBestResponseCap reward roots who 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (quittingAbsolutePureTime start passport) 0 := by
  let survival := quittingOpponentSurvivalWeight roots who 0 start
  let suffixValue : Option ℕ → ℝ := fun quitTime ↦
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime start
  let sourceValue : Option ℕ → ℝ := fun quitTime ↦
    quittingRootSequencePureTimeTerminalValue reward roots who
      (quittingAbsolutePureTime start quitTime) 0
  let suffixCap : ℝ := sSup (Set.range suffixValue)
  let sourceCap : ℝ := sSup (Set.range fun quitTime : Option ℕ =>
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0)
  have hsurvival : 0 ≤ survival := by
    exact quittingOpponentSurvivalWeight_nonneg roots who 0 start
  have hsurvival_le_one : survival ≤ 1 := by
    exact quittingOpponentSurvivalWeight_le_one roots who 0 start
  have htransport' : ∀ first second,
      survival * (suffixValue first - suffixValue second) =
        sourceValue first - sourceValue second := by
    intro first second
    exact htransport start first second
  have hsuffixNonempty : (Set.range suffixValue).Nonempty := by
    exact ⟨suffixValue none, ⟨none, rfl⟩⟩
  have hsourceValue_le : ∀ quitTime, sourceValue quitTime ≤ sourceCap := by
    intro quitTime
    dsimp [sourceValue, sourceCap]
    exact le_csSup hsource ⟨quittingAbsolutePureTime start quitTime, rfl⟩
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

/-- Absolute-date form of the suffix regret inequality.  The source passport
is a finite quit date `quitTime`, while the reached suffix sees the remaining
date `quitTime - start`. -/
theorem quittingPureTimeSuffixRegret_le_of_prefixTransport_at_absoluteQuitTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start quitTime : ℕ)
    (hstart : start ≤ quitTime)
    (htransport : IsQuittingPureTimePrefixTransport reward roots who)
    (hsource : BddAbove (Set.range fun choice : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who choice 0))
    (hsuffix : BddAbove (Set.range fun choice : Option ℕ =>
      quittingRootSequencePureTimeTerminalValue reward roots who choice start)) :
    quittingOpponentSurvivalWeight roots who 0 start *
        (quittingPureTimeBestResponseCap reward roots who start -
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some (quitTime - start)) start) ≤
      quittingPureTimeBestResponseCap reward roots who 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who
          (some quitTime) 0 := by
  have hmain := quittingPureTimeSuffixRegret_le_of_prefixTransport
    reward roots who start (some (quitTime - start)) htransport hsource hsuffix
  simpa [quittingAbsolutePureTime, Nat.add_sub_of_le hstart] using hmain

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
    (h₁ : BddAbove (Set.range (quittingPureTimeFaceValue reward faces one who)))
    (h₂ : BddAbove (Set.range (quittingPureTimeFaceValue reward faces two who)))
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
  exact Math.Optimization.upperToBase_regret_ge_supMixedDifference_sub
    (quittingPureTimeFaceValue reward faces base who)
    (quittingPureTimeFaceValue reward faces one who)
    (quittingPureTimeFaceValue reward faces two who)
    (quittingPureTimeFaceValue reward faces both who)
    h₁ h₂ q eta quitTime hface hupper

/-! ## Explicit chronology input -/

/-- A named conditional input for a chronological renewal consumer.  The
fields separate source return, survival-weighted continuation residual, and
passport alignment; no theorem in this file constructs them from a radial
reset cube. -/
structure QuittingChronologicalRenewalInput
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  phases : ℕ
  sourceReturnError : ℝ
  weightedContinueResidual : ℝ
  passportError : ℝ
  opponentSurvivalProduct : ι → ℝ
  sourceReturnError_nonneg : 0 ≤ sourceReturnError
  weightedContinueResidual_nonneg : 0 ≤ weightedContinueResidual
  passportError_nonneg : 0 ≤ passportError
  opponentSurvivalProduct_nonneg : ∀ who, 0 ≤ opponentSurvivalProduct who
  opponentSurvivalProduct_lt_one : ∀ who, opponentSurvivalProduct who < 1

end GameTheory
