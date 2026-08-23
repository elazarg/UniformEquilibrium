/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.SurvivalProduct
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Boundary.Repair.PunishmentFloorClip
import UniformEquilibrium.Quitting.Classification.Existence.WellSupportedAbsorbingSequence
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SuppliedCorrespondence
import UniformEquilibrium.Quitting.Root.FirstBranch
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-!
# Floor-clipped purification at a survival crossing

This module isolates the local repair of the discontinuous first-crossing
argument used in the corrected Simon finite-orbit program.  It does not prove
the corrected uniform survival constant, produce the conditioned row from an
arbitrary behavioral equilibrium, or prove Simon's Theorem 3.

The actual continuation profile is retained long enough to show that clipping
its payoff at the punishment floor is attainable by unilateral continuation
deviations.  A simultaneous pure-support replacement then deletes only actions
whose played mass is quantitatively small.  Endpoint stability, a no-sure-
quitter exclusion, and the corrected uniform survival constant are deliberately
separate supplied hypotheses.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Clip an actual tail at the punishment floor with slack `η`. -/
def quittingPunishmentFloorClipAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (η : ℝ) (tail : Payoff ι) : Payoff ι :=
  fun who => max (tail who) (quittingPunishmentValue reward who - η)

@[simp] theorem quittingPunishmentFloorClipAt_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (η : ℝ) (tail : Payoff ι) (who : ι) :
    quittingPunishmentFloorClipAt reward η tail who =
      max (tail who) (quittingPunishmentValue reward who - η) := rfl

/-- The slack floor clip dominates the actual tail coordinatewise. -/
theorem le_quittingPunishmentFloorClipAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (η : ℝ) (tail : Payoff ι) (who : ι) :
    tail who ≤ quittingPunishmentFloorClipAt reward η tail who :=
  le_max_left _ _

/-- The slack floor clip is individually rational at the displayed slack. -/
theorem quittingSimonRationalPayoffAt_quittingPunishmentFloorClipAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (η : ℝ) (tail : Payoff ι) :
    QuittingSimonRationalPayoffAt reward η
      (quittingPunishmentFloorClipAt reward η tail) := by
  intro who
  exact le_max_right _ _

/-- Clipping changes nothing when the actual tail already satisfies the same
individual-rationality inequality. -/
theorem quittingPunishmentFloorClipAt_eq_self_of_rational
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (η : ℝ) (tail : Payoff ι)
    (hrational : QuittingSimonRationalPayoffAt reward η tail) :
    quittingPunishmentFloorClipAt reward η tail = tail := by
  funext who
  exact max_eq_left (hrational who)

/-- The slack floor clip is a translated use of the production punishment
floor clip. -/
theorem quittingPunishmentFloorClipAt_eq_sub_clip_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (η : ℝ) (tail : Payoff ι) :
    quittingPunishmentFloorClipAt reward η tail =
      fun who => quittingPunishmentFloorClip reward
        (fun player => tail player + η) who - η := by
  funext who
  simp only [quittingPunishmentFloorClipAt_apply,
    quittingPunishmentFloorClip_apply]
  rw [← max_sub_sub_right]
  ring_nf
  rw [max_comm]

/-- A floor-clipped coordinate of an actual continuation payoff is attained
from below by an actual unilateral continuation deviation.  No best-response
supremum is assumed to be attained. -/
theorem exists_quittingContinuation_deviation_ge_floorClip
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {η : ℝ} (hη : 0 < η) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingPunishmentFloorClipAt reward η
          (fun player => quittingTerminalPayoff reward continuation player) who ≤
        quittingTerminalPayoff reward
          (Function.update continuation who deviation) who := by
  let tail : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  by_cases hclip : quittingPunishmentFloorClipAt reward η tail who ≤ tail who
  · refine ⟨continuation who, ?_⟩
    simpa [tail] using hclip
  · have hfloor :
        quittingPunishmentFloorClipAt reward η tail who =
          quittingPunishmentValue reward who - η := by
      rw [quittingPunishmentFloorClipAt_apply, max_eq_right]
      apply le_of_not_ge
      intro hfloorLe
      apply hclip
      rw [quittingPunishmentFloorClipAt_apply, max_eq_left hfloorLe]
    have hpunish := quittingPunishmentValue_le reward who continuation
    have hbest : quittingPunishmentValue reward who ≤
        quittingContinuationBestResponseValue reward continuation who := by
      simpa only [quittingBestReplyValue, quittingContinuationBestResponseValue,
        sSup_range] using hpunish
    let δ := quittingContinuationBestResponseValue reward continuation who -
      quittingPunishmentFloorClipAt reward η tail who
    have hδ : 0 < δ := by
      dsimp only [δ]
      rw [hfloor]
      linarith
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub
        reward continuation who hδ
    refine ⟨deviation, ?_⟩
    dsimp only [δ] at hdeviation
    linarith

/-- Behavioral Nash of the actual root/continuation splice bounds the pure
Quit endpoint of the actual-tail row. -/
theorem quittingRootQuitPayoff_le_successor_add_of_spliceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (ε : ℝ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingRootThenContinuationProfile reward root continuation))
    (who : ι) :
    quittingRootQuitPayoff reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who ≤
      quittingRootSuccessorPayoff reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who + ε := by
  let deviation := quittingRootAndContinuationDeviation reward
    (PMF.pure true) (continuation who)
  have hdeviation := hnash who deviation
  have hpayoff :=
    quittingTerminalPayoff_update_rootAndContinuationDeviation_eq
      reward root continuation who (PMF.pure true) (continuation who)
  have hprescribed :=
    quittingTerminalPayoff_rootThenContinuation_eq
      reward root continuation who
  dsimp only [deviation] at hdeviation
  rw [hpayoff, hprescribed] at hdeviation
  simpa [quittingRootQuitPayoff, quittingRootSuccessorPayoff] using hdeviation

/-- Behavioral Nash of the actual root/continuation splice also bounds the
pure Continue endpoint after floor clipping.  The proof uses an actual tail
deviation approaching the best-response supremum. -/
theorem quittingRootContinuePayoff_floorClip_le_successor_add_of_spliceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {η : ℝ} (hη : 0 < η) (ε : ℝ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingRootThenContinuationProfile reward root continuation))
    (who : ι) :
    quittingRootContinuePayoff reward
        (quittingPunishmentFloorClipAt reward η
          (fun player => quittingTerminalPayoff reward continuation player))
        root who ≤
      quittingRootSuccessorPayoff reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who + ε := by
  obtain ⟨continuationDeviation, hclip⟩ :=
    exists_quittingContinuation_deviation_ge_floorClip
      reward continuation who hη
  let deviation := quittingRootAndContinuationDeviation reward
    (PMF.pure false) continuationDeviation
  have hnashDeviation := hnash who deviation
  have hdeviation :=
    quittingTerminalPayoff_update_rootAndContinuationDeviation_eq
      reward root continuation who (PMF.pure false) continuationDeviation
  have hprescribed :=
    quittingTerminalPayoff_rootThenContinuation_eq
      reward root continuation who
  have hmonotone := quittingRootExpectedPayoff_continuation_le_add reward
    (quittingPunishmentFloorClipAt reward η
      (fun player => quittingTerminalPayoff reward continuation player))
    (Function.update
      (fun player => quittingTerminalPayoff reward continuation player)
      who
      (quittingTerminalPayoff reward
        (Function.update continuation who continuationDeviation) who))
    (Function.update root who (PMF.pure false)) who (δ := 0) le_rfl (by
      simpa using hclip)
  dsimp only [deviation] at hnashDeviation
  rw [hdeviation, hprescribed] at hnashDeviation
  change quittingRootContinuePayoff reward
      (quittingPunishmentFloorClipAt reward η
        (fun player => quittingTerminalPayoff reward continuation player))
      root who ≤ _ at hmonotone
  change quittingRootContinuePayoff reward
      (quittingPunishmentFloorClipAt reward η
        (fun player => quittingTerminalPayoff reward continuation player))
      root who ≤
    quittingRootExpectedPayoff reward
      (fun player => quittingTerminalPayoff reward continuation player)
      root who + ε
  linarith

/-! ## Simultaneous support purification -/

/-- Quit is strictly inferior by more than `β` at the clipped row. -/
def IsQuittingRootBadQuitAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι) : Prop :=
  quittingRootQuitPayoff reward tail root who <
    quittingRootContinuePayoff reward tail root who - β

/-- Continue is strictly inferior by more than `β` at the clipped row. -/
def IsQuittingRootBadContinueAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι) : Prop :=
  quittingRootContinuePayoff reward tail root who <
    quittingRootQuitPayoff reward tail root who - β

/-- Simultaneously delete every action which is inferior by more than `β`.
Coordinates with no strict deletion remain unchanged. -/
def quittingSupportPurifiedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) : ι → PMF Bool := by
  classical
  exact fun who =>
    if IsQuittingRootBadQuitAt reward tail β root who then PMF.pure false
    else if IsQuittingRootBadContinueAt reward tail β root who then PMF.pure true
    else root who

@[simp] theorem quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι)
    (hbad : IsQuittingRootBadQuitAt reward tail β root who) :
    quittingSupportPurifiedRoot reward tail β root who = PMF.pure false := by
  simp [quittingSupportPurifiedRoot, hbad]

@[simp] theorem quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι)
    (hnotBadQuit : ¬IsQuittingRootBadQuitAt reward tail β root who)
    (hbad : IsQuittingRootBadContinueAt reward tail β root who) :
    quittingSupportPurifiedRoot reward tail β root who = PMF.pure true := by
  simp [quittingSupportPurifiedRoot, hnotBadQuit, hbad]

@[simp] theorem quittingSupportPurifiedRoot_eq_self_of_not_bad
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι)
    (hnotBadQuit : ¬IsQuittingRootBadQuitAt reward tail β root who)
    (hnotBadContinue : ¬IsQuittingRootBadContinueAt reward tail β root who) :
    quittingSupportPurifiedRoot reward tail β root who = root who := by
  simp [quittingSupportPurifiedRoot, hnotBadQuit, hnotBadContinue]

/-- Opponent endpoint payoffs are stable when every displayed Quit
probability is perturbed by less than `d`.  Compactness supplies such a
modulus in applications; the local repair consumes it explicitly. -/
def IsQuittingRootEndpointStableWithin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (d e : ℝ) : Prop :=
  ∀ candidate : ι → PMF Bool,
    (∀ who, |(candidate who true).toReal - (root who true).toReal| < d) →
      ∀ who,
        |quittingRootQuitPayoff reward tail candidate who -
            quittingRootQuitPayoff reward tail root who| ≤ e ∧
          |quittingRootContinuePayoff reward tail candidate who -
            quittingRootContinuePayoff reward tail root who| ≤ e

/-- Raising a tail coordinate raises the corresponding pure Continue
endpoint. -/
theorem quittingRootContinuePayoff_mono_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : Payoff ι} (h : ∀ who, first who ≤ second who)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward first root who ≤
      quittingRootContinuePayoff reward second root who := by
  simpa [quittingRootContinuePayoff] using
    (quittingRootExpectedPayoff_continuation_le_add reward first second
      (Function.update root who (PMF.pure false)) who (δ := 0) le_rfl
        (by simpa using h who))

/-- If both pure endpoints are bounded by the actual successor up to positive
error, every played strictly inferior Quit action has small probability. -/
theorem badQuit_quitProbability_mul_lt_of_endpointCaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (actual clipped : Payoff ι) (root : ι → PMF Bool)
    {β ε : ℝ} (hε : 0 < ε) (htail : ∀ who, actual who ≤ clipped who)
    (hcontinue : ∀ who,
      quittingRootContinuePayoff reward clipped root who ≤
        quittingRootSuccessorPayoff reward actual root who + ε)
    (who : ι) (hbad : IsQuittingRootBadQuitAt reward clipped β root who) :
    (root who true).toReal * β < ε := by
  have hactualContinue := quittingRootContinuePayoff_mono_tail
    reward htail root who
  have hactualQuit : quittingRootQuitPayoff reward actual root who =
      quittingRootQuitPayoff reward clipped root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward actual clipped root who
  have hcap := hcontinue who
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward actual root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  by_cases hquit : (root who true).toReal = 0
  · simp [hquit, hε]
  · have hquitPos : 0 < (root who true).toReal :=
      lt_of_le_of_ne hquitNonneg (Ne.symm hquit)
    have hcontinueScaled := mul_le_mul_of_nonneg_left
      hactualContinue hcontinueNonneg
    have hgap : β < quittingRootContinuePayoff reward clipped root who -
        quittingRootQuitPayoff reward actual root who := by
      dsimp only [IsQuittingRootBadQuitAt] at hbad
      rw [hactualQuit]
      linarith
    have hregret : (root who true).toReal *
        (quittingRootContinuePayoff reward clipped root who -
          quittingRootQuitPayoff reward actual root who) ≤ ε := by
      have hdecomp :
          (root who true).toReal *
              quittingRootContinuePayoff reward clipped root who +
            (root who false).toReal *
              quittingRootContinuePayoff reward clipped root who =
            quittingRootContinuePayoff reward clipped root who := by
        calc
          _ = ((root who false).toReal + (root who true).toReal) *
              quittingRootContinuePayoff reward clipped root who := by ring
          _ = _ := by rw [hsum, one_mul]
      rw [hmix] at hcap
      linarith
    have hscaled := mul_lt_mul_of_pos_left hgap hquitPos
    nlinarith

/-- Under the same endpoint caps, every played strictly inferior Continue
action has small probability. -/
theorem badContinue_continueProbability_mul_lt_of_endpointCaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (actual clipped : Payoff ι) (root : ι → PMF Bool)
    {β ε : ℝ} (hε : 0 < ε) (htail : ∀ who, actual who ≤ clipped who)
    (hquit : ∀ who,
      quittingRootQuitPayoff reward actual root who ≤
        quittingRootSuccessorPayoff reward actual root who + ε)
    (who : ι) (hbad : IsQuittingRootBadContinueAt reward clipped β root who) :
    (root who false).toReal * β < ε := by
  have hactualContinue := quittingRootContinuePayoff_mono_tail
    reward htail root who
  have hactualQuit : quittingRootQuitPayoff reward actual root who =
      quittingRootQuitPayoff reward clipped root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward actual clipped root who
  have hcap := hquit who
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward actual root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  by_cases hcontinue : (root who false).toReal = 0
  · rw [hcontinue, zero_mul]
    exact hε
  · have hcontinuePos : 0 < (root who false).toReal :=
      lt_of_le_of_ne hcontinueNonneg (Ne.symm hcontinue)
    have hcontinueScaled := mul_le_mul_of_nonneg_left
      hactualContinue hcontinueNonneg
    have hgap : β < quittingRootQuitPayoff reward actual root who -
        quittingRootContinuePayoff reward actual root who := by
      dsimp only [IsQuittingRootBadContinueAt] at hbad
      rw [hactualQuit]
      linarith
    rw [hactualQuit] at hcap hmix
    have hregret : (root who false).toReal *
        (quittingRootQuitPayoff reward clipped root who -
          quittingRootContinuePayoff reward actual root who) ≤ ε := by
      have hdecomp :
          (root who true).toReal *
              quittingRootQuitPayoff reward clipped root who +
            (root who false).toReal *
              quittingRootQuitPayoff reward clipped root who =
            quittingRootQuitPayoff reward clipped root who := by
        calc
          _ = ((root who false).toReal + (root who true).toReal) *
              quittingRootQuitPayoff reward clipped root who := by ring
          _ = _ := by rw [hsum, one_mul]
      rw [hmix] at hcap
      linarith
    have hscaled := mul_lt_mul_of_pos_left hgap hcontinuePos
    rw [hactualQuit] at hscaled
    nlinarith

/-- With nonnegative separation, Quit and Continue cannot both be strictly
inferior at the same coordinate. -/
theorem not_badContinue_of_badQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {β : ℝ} (hβ : 0 ≤ β)
    (root : ι → PMF Bool) (who : ι)
    (hbad : IsQuittingRootBadQuitAt reward tail β root who) :
    ¬IsQuittingRootBadContinueAt reward tail β root who := by
  intro hbadContinue
  dsimp only [IsQuittingRootBadQuitAt] at hbad
  dsimp only [IsQuittingRootBadContinueAt] at hbadContinue
  linarith

/-- Quantitative deletion bounds imply coordinatewise closeness of the
simultaneously purified root. -/
theorem supportPurifiedRoot_coordinate_close_of_badAction_small
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β d : ℝ) (root : ι → PMF Bool) (hd : 0 < d)
    (hbadQuit : ∀ who, IsQuittingRootBadQuitAt reward tail β root who →
      (root who true).toReal < d)
    (hbadContinue : ∀ who,
      IsQuittingRootBadContinueAt reward tail β root who →
        (root who false).toReal < d) :
    ∀ who,
      |(quittingSupportPurifiedRoot reward tail β root who true).toReal -
          (root who true).toReal| < d := by
  classical
  intro who
  by_cases hq : IsQuittingRootBadQuitAt reward tail β root who
  · rw [quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
      reward tail β root who hq]
    simpa [abs_of_nonneg ENNReal.toReal_nonneg] using hbadQuit who hq
  · by_cases hc : IsQuittingRootBadContinueAt reward tail β root who
    · rw [quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
        reward tail β root who hq hc]
      simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
      have hsum := quittingRoot_continueProbability_add_quitProbability root who
      have hquitLe : (root who true).toReal ≤ 1 := by
        have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hquitLe)]
      linarith [hbadContinue who hc]
    · rw [quittingSupportPurifiedRoot_eq_self_of_not_bad
        reward tail β root who hq hc]
      simpa using hd

/-- Multiplicative small-mass estimates at scale `α / u`, together with
`α < u * β * d`, give the coordinate closeness needed by endpoint stability. -/
theorem supportPurifiedRoot_coordinate_close_of_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    {α u β d : ℝ} (hu : 0 < u) (hβ : 0 < β) (hd : 0 < d)
    (hscale : α < u * β * d)
    (hbadQuit : ∀ who, IsQuittingRootBadQuitAt reward tail β root who →
      (root who true).toReal * β < α / u)
    (hbadContinue : ∀ who,
      IsQuittingRootBadContinueAt reward tail β root who →
        (root who false).toReal * β < α / u) :
    ∀ who,
      |(quittingSupportPurifiedRoot reward tail β root who true).toReal -
          (root who true).toReal| < d := by
  apply supportPurifiedRoot_coordinate_close_of_badAction_small
    reward tail β d root hd
  · intro who hbad
    have hmul := (lt_div_iff₀ hu).mp (hbadQuit who hbad)
    by_contra hnot
    have hdq : d ≤ (root who true).toReal := le_of_not_gt hnot
    have hβq : d * β ≤ (root who true).toReal * β :=
      mul_le_mul_of_nonneg_right hdq hβ.le
    have huq : d * β * u ≤ (root who true).toReal * β * u :=
      mul_le_mul_of_nonneg_right hβq hu.le
    nlinarith
  · intro who hbad
    have hmul := (lt_div_iff₀ hu).mp (hbadContinue who hbad)
    by_contra hnot
    have hdq : d ≤ (root who false).toReal := le_of_not_gt hnot
    have hβq : d * β ≤ (root who false).toReal * β :=
      mul_le_mul_of_nonneg_right hdq hβ.le
    have huq : d * β * u ≤ (root who false).toReal * β * u :=
      mul_le_mul_of_nonneg_right hβq hu.le
    nlinarith

/-- Endpoint stability turns simultaneous deletion of the strictly inferior
actions into support-local `η`-optimality. -/
theorem isQuittingRootSupportApproxNash_supportPurifiedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    {β d e η : ℝ} (hβ : 0 ≤ β) (herror : β + 2 * e ≤ η)
    (hstable : IsQuittingRootEndpointStableWithin reward tail root d e)
    (hclose : ∀ who,
      |(quittingSupportPurifiedRoot reward tail β root who true).toReal -
          (root who true).toReal| < d) :
    IsQuittingRootSupportApproxNash reward tail η
      (quittingSupportPurifiedRoot reward tail β root) := by
  classical
  let purified := quittingSupportPurifiedRoot reward tail β root
  have hendpoint := hstable purified hclose
  intro who
  constructor
  · intro hquitPositive
    have hnotBad : ¬IsQuittingRootBadQuitAt reward tail β root who := by
      intro hbad
      have hpure := quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
        reward tail β root who hbad
      rw [hpure] at hquitPositive
      simp at hquitPositive
    have hrootDifference : -β ≤
        quittingRootEndpointDifference reward tail root who := by
      dsimp only [IsQuittingRootBadQuitAt] at hnotBad
      unfold quittingRootEndpointDifference
      linarith
    have hquitClose := (hendpoint who).1
    have hcontinueClose := (hendpoint who).2
    dsimp only [quittingRootEndpointDifference] at hrootDifference ⊢
    rw [abs_le] at hquitClose hcontinueClose
    dsimp only [purified] at hquitClose hcontinueClose
    linarith
  · intro hcontinuePositive
    have hnotBad : ¬IsQuittingRootBadContinueAt reward tail β root who := by
      intro hbad
      have hnotBadQuit : ¬IsQuittingRootBadQuitAt reward tail β root who := by
        intro hbadQuit
        exact not_badContinue_of_badQuit reward tail hβ root who hbadQuit hbad
      have hpure := quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
        reward tail β root who hnotBadQuit hbad
      rw [hpure] at hcontinuePositive
      simp at hcontinuePositive
    have hrootDifference :
        quittingRootEndpointDifference reward tail root who ≤ β := by
      dsimp only [IsQuittingRootBadContinueAt] at hnotBad
      unfold quittingRootEndpointDifference
      linarith
    have hquitClose := (hendpoint who).1
    have hcontinueClose := (hendpoint who).2
    dsimp only [quittingRootEndpointDifference] at hrootDifference ⊢
    rw [abs_le] at hquitClose hcontinueClose
    dsimp only [purified] at hquitClose hcontinueClose
    linarith

/-! ## Explicit compact-carrier inputs -/

/-- Supplied exclusion of a sure quitter at one rational support-local scale.
This is intentionally a hypothesis, not a theorem about the game. -/
def SuppliedQuittingSimonNoSureQuitterAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ : ℝ) : Prop :=
  ∀ tail root,
    QuittingSimonRationalPayoffAt reward σ tail →
      IsQuittingRootSupportApproxNash reward tail σ root →
        ¬QuittingRootHasSureQuitter root

/-- The corrected uniform survival constant on the normalized Simon carrier.
The compactness proof supplying this implication is outside this module. -/
def SuppliedQuittingSimonCorrectedUniformSurvivalAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ρ : ℝ) : Prop :=
  ∀ tail,
    QuittingSimonNearFeasiblePayoffAt reward 1 tail →
      QuittingSimonRationalPayoffAt reward ρ tail →
        ∀ root,
          IsQuittingRootSupportApproxNash reward tail ρ root →
            ρ ≤ quittingStationaryContinueMass root

/-- Individual rationality is monotone in its error tolerance. -/
theorem QuittingSimonRationalPayoffAt.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {first second : ℝ} {tail : Payoff ι}
    (hrational : QuittingSimonRationalPayoffAt reward first tail)
    (hle : first ≤ second) :
    QuittingSimonRationalPayoffAt reward second tail := by
  intro who
  have hwho := hrational who
  linarith

/-- The supplied no-sure-quitter exclusion rules out every bad Continue
coordinate of the purified root. -/
theorem no_badContinue_supportPurifiedRoot_of_suppliedNoSure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    {β η σ : ℝ} (hβ : 0 ≤ β) (hησ : η ≤ σ)
    (hrational : QuittingSimonRationalPayoffAt reward η tail)
    (hsupport : IsQuittingRootSupportApproxNash reward tail η
      (quittingSupportPurifiedRoot reward tail β root))
    (hnoSure : SuppliedQuittingSimonNoSureQuitterAt reward σ) :
    ∀ who, ¬IsQuittingRootBadContinueAt reward tail β root who := by
  classical
  let purified := quittingSupportPurifiedRoot reward tail β root
  have hrationalσ := hrational.mono hησ
  have hsupportσ := hsupport.mono hησ
  have hnotSure := hnoSure tail purified hrationalσ hsupportσ
  intro who hbad
  have hnotBadQuit : ¬IsQuittingRootBadQuitAt reward tail β root who := by
    intro hbadQuit
    exact not_badContinue_of_badQuit reward tail hβ root who hbadQuit hbad
  have hpure := quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
    reward tail β root who hnotBadQuit hbad
  apply hnotSure
  exact ⟨who, hpure⟩

/-- Once bad Continue coordinates are excluded, purification only deletes
Quit mass. -/
theorem supportPurifiedRoot_quitProbability_le_of_no_badContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool)
    (hnoBadContinue : ∀ who,
      ¬IsQuittingRootBadContinueAt reward tail β root who) :
    ∀ who,
      (quittingSupportPurifiedRoot reward tail β root who true).toReal ≤
        (root who true).toReal := by
  classical
  intro who
  by_cases hbadQuit : IsQuittingRootBadQuitAt reward tail β root who
  · rw [quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
      reward tail β root who hbadQuit]
    simp
  · rw [quittingSupportPurifiedRoot_eq_self_of_not_bad
      reward tail β root who hbadQuit (hnoBadContinue who)]

/-- The same one-sided purification increases every Continue probability. -/
theorem le_supportPurifiedRoot_continueProbability_of_no_badContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool)
    (hnoBadContinue : ∀ who,
      ¬IsQuittingRootBadContinueAt reward tail β root who) :
    ∀ who,
      (root who false).toReal ≤
        (quittingSupportPurifiedRoot reward tail β root who false).toReal := by
  intro who
  have hroot := quittingRoot_continueProbability_add_quitProbability root who
  have hpurified := quittingRoot_continueProbability_add_quitProbability
    (quittingSupportPurifiedRoot reward tail β root) who
  have hquit := supportPurifiedRoot_quitProbability_le_of_no_badContinue
    reward tail β root hnoBadContinue who
  linarith

/-- The corrected uniform-survival input applies to the purified clipped row
after monotonicity of the rational and support tolerances. -/
theorem rho_le_continueMass_supportPurifiedRoot_of_suppliedUniformSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    {β η ρ : ℝ} (hηρ : η ≤ ρ)
    (hnear : QuittingSimonNearFeasiblePayoffAt reward 1 tail)
    (hrational : QuittingSimonRationalPayoffAt reward η tail)
    (hsupport : IsQuittingRootSupportApproxNash reward tail η
      (quittingSupportPurifiedRoot reward tail β root))
    (huniform : SuppliedQuittingSimonCorrectedUniformSurvivalAt reward ρ) :
    ρ ≤ quittingStationaryContinueMass
      (quittingSupportPurifiedRoot reward tail β root) := by
  exact huniform tail hnear (hrational.mono hηρ)
    _ (hsupport.mono hηρ)

/-! ## Product survival loss -/

/-- The product survival gained by deleting Quit mass is at most the sum of
the deleted marginal Quit probabilities. -/
theorem continueMass_supportPurifiedRoot_sub_le_sum_deletedQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool)
    (hnoBadContinue : ∀ who,
      ¬IsQuittingRootBadContinueAt reward tail β root who) :
    quittingStationaryContinueMass
        (quittingSupportPurifiedRoot reward tail β root) -
        quittingStationaryContinueMass root ≤
      ∑ who,
        ((root who true).toReal -
          (quittingSupportPurifiedRoot reward tail β root who true).toReal) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  calc
    _ ≤ ∑ who,
        ((quittingSupportPurifiedRoot reward tail β root who false).toReal -
          (root who false).toReal) := by
      apply Math.prod_sub_prod_le_sum_sub_of_le Finset.univ
      · intro who _
        exact ENNReal.toReal_nonneg
      · intro who _
        have hsum := quittingRoot_continueProbability_add_quitProbability root who
        have hquit : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
        linarith
      · intro who _
        exact ENNReal.toReal_nonneg
      · intro who _
        have hsum := quittingRoot_continueProbability_add_quitProbability
          (quittingSupportPurifiedRoot reward tail β root) who
        have hquit : 0 ≤
            (quittingSupportPurifiedRoot reward tail β root who true).toReal :=
          ENNReal.toReal_nonneg
        linarith
      · intro who _
        exact le_supportPurifiedRoot_continueProbability_of_no_badContinue
          reward tail β root hnoBadContinue who
    _ = _ := by
      apply Finset.sum_congr rfl
      intro who _
      have hroot := quittingRoot_continueProbability_add_quitProbability root who
      have hpurified := quittingRoot_continueProbability_add_quitProbability
        (quittingSupportPurifiedRoot reward tail β root) who
      linarith

/-- A uniform bound on deleted Quit mass gives the card-times-error survival
loss used at the first crossing. -/
theorem continueMass_supportPurifiedRoot_sub_le_card_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β bound : ℝ) (root : ι → PMF Bool)
    (hnoBadContinue : ∀ who,
      ¬IsQuittingRootBadContinueAt reward tail β root who)
    (hdeleted : ∀ who,
      (root who true).toReal -
          (quittingSupportPurifiedRoot reward tail β root who true).toReal ≤
        bound) :
    quittingStationaryContinueMass
        (quittingSupportPurifiedRoot reward tail β root) -
        quittingStationaryContinueMass root ≤
      Fintype.card ι * bound := by
  refine (continueMass_supportPurifiedRoot_sub_le_sum_deletedQuit
    reward tail β root hnoBadContinue).trans ?_
  calc
    (∑ who,
        ((root who true).toReal -
          (quittingSupportPurifiedRoot reward tail β root who true).toReal)) ≤
        ∑ _who : ι, bound := Finset.sum_le_sum fun who _ => hdeleted who
    _ = Fintype.card ι * bound := by simp

/-- Equivalent absorption form of the card-times-deleted-hazard estimate. -/
theorem absorptionMass_sub_supportPurifiedRoot_le_card_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β bound : ℝ) (root : ι → PMF Bool)
    (hnoBadContinue : ∀ who,
      ¬IsQuittingRootBadContinueAt reward tail β root who)
    (hdeleted : ∀ who,
      (root who true).toReal -
          (quittingSupportPurifiedRoot reward tail β root who true).toReal ≤
        bound) :
    quittingRootAbsorptionMass root -
        quittingRootAbsorptionMass
          (quittingSupportPurifiedRoot reward tail β root) ≤
      Fintype.card ι * bound := by
  have hcontinue := continueMass_supportPurifiedRoot_sub_le_card_mul
    reward tail β bound root hnoBadContinue hdeleted
  unfold quittingRootAbsorptionMass
  linarith

/-! ## Audited local row theorem -/

/-- The reusable output of the floor-clipped row repair.  `loss` is the
explicit one-row survival loss, not an asymptotic or accumulated prefix error. -/
structure QuittingFloorClippedPurificationCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (d η ρ loss : ℝ)
    (original purified : ι → PMF Bool) : Prop where
  rational : QuittingSimonRationalPayoffAt reward η tail
  support : IsQuittingRootSupportApproxNash reward tail η purified
  coordinateClose : ∀ who,
    |(purified who true).toReal - (original who true).toReal| < d
  noSureQuitter : ¬QuittingRootHasSureQuitter purified
  quitProbability_le : ∀ who,
    (purified who true).toReal ≤ (original who true).toReal
  purifiedContinue_lower : ρ ≤ quittingStationaryContinueMass purified
  continueMassLoss_le :
    quittingStationaryContinueMass purified -
      quittingStationaryContinueMass original ≤ loss

/-- The certificate's lower bound and loss estimate give the corresponding
lower bound for the original, unpurified row. -/
theorem QuittingFloorClippedPurificationCertificate.originalContinue_lower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {d η ρ loss : ℝ}
    {original purified : ι → PMF Bool}
    (certificate : QuittingFloorClippedPurificationCertificate reward tail
      d η ρ loss original purified) :
    ρ - loss ≤ quittingStationaryContinueMass original := by
  linarith [certificate.purifiedContinue_lower,
    certificate.continueMassLoss_le]

/-- **Floor-clipped survival-row repair.**  Starting from an actual behavioral
root/continuation splice, this theorem constructs the simultaneous support
purification and proves the quantitative one-row survival lower bound.

The endpoint modulus, no-sure-quitter exclusion, normalized near-feasibility,
and corrected uniform survival constant are explicit inputs.  The theorem does
not produce a global conditioned prefix or a finite orbit.  Its `0 < α`
hypothesis is deliberate: the exact zero-error case is not covered by the
strict small-deletion argument. -/
theorem floorClippedPurificationCertificate_of_spliceNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {α u β d e η σ ρ : ℝ}
    (hα : 0 < α) (hu : 0 < u) (hβ : 0 < β) (hd : 0 < d)
    (hη : 0 < η) (hscale : α < u * β * d)
    (hendpointError : β + 2 * e ≤ η)
    (hησ : η ≤ σ) (hηρ : η ≤ ρ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (α / u)
      (quittingRootThenContinuationProfile reward root continuation))
    (hstable : IsQuittingRootEndpointStableWithin reward
      (quittingPunishmentFloorClipAt reward η
        (fun who => quittingTerminalPayoff reward continuation who))
      root d e)
    (hnear : QuittingSimonNearFeasiblePayoffAt reward 1
      (quittingPunishmentFloorClipAt reward η
        (fun who => quittingTerminalPayoff reward continuation who)))
    (hnoSure : SuppliedQuittingSimonNoSureQuitterAt reward σ)
    (huniform : SuppliedQuittingSimonCorrectedUniformSurvivalAt reward ρ) :
    QuittingFloorClippedPurificationCertificate reward
      (quittingPunishmentFloorClipAt reward η
        (fun who => quittingTerminalPayoff reward continuation who))
      d η ρ (Fintype.card ι * α / (u * β)) root
      (quittingSupportPurifiedRoot reward
        (quittingPunishmentFloorClipAt reward η
          (fun who => quittingTerminalPayoff reward continuation who))
        β root) := by
  let actual : Payoff ι :=
    fun who => quittingTerminalPayoff reward continuation who
  let clipped := quittingPunishmentFloorClipAt reward η actual
  let purified := quittingSupportPurifiedRoot reward clipped β root
  have hε : 0 < α / u := div_pos hα hu
  have htail : ∀ who, actual who ≤ clipped who := by
    intro who
    exact le_quittingPunishmentFloorClipAt reward η actual who
  have hquitCap : ∀ who,
      quittingRootQuitPayoff reward actual root who ≤
        quittingRootSuccessorPayoff reward actual root who + α / u := by
    intro who
    exact quittingRootQuitPayoff_le_successor_add_of_spliceNash
      reward root continuation (α / u) hnash who
  have hcontinueCap : ∀ who,
      quittingRootContinuePayoff reward clipped root who ≤
        quittingRootSuccessorPayoff reward actual root who + α / u := by
    intro who
    exact quittingRootContinuePayoff_floorClip_le_successor_add_of_spliceNash
      reward root continuation hη (α / u) hnash who
  have hbadQuit : ∀ who,
      IsQuittingRootBadQuitAt reward clipped β root who →
        (root who true).toReal * β < α / u := by
    intro who hbad
    exact badQuit_quitProbability_mul_lt_of_endpointCaps
      reward actual clipped root hε htail hcontinueCap who hbad
  have hbadContinue : ∀ who,
      IsQuittingRootBadContinueAt reward clipped β root who →
        (root who false).toReal * β < α / u := by
    intro who hbad
    exact badContinue_continueProbability_mul_lt_of_endpointCaps
      reward actual clipped root hε htail hquitCap who hbad
  have hclose : ∀ who,
      |(purified who true).toReal - (root who true).toReal| < d := by
    exact supportPurifiedRoot_coordinate_close_of_mul_bound
      reward clipped root hu hβ hd hscale hbadQuit hbadContinue
  have hsupport : IsQuittingRootSupportApproxNash reward clipped η purified := by
    exact isQuittingRootSupportApproxNash_supportPurifiedRoot
      reward clipped root hβ.le hendpointError hstable hclose
  have hrational : QuittingSimonRationalPayoffAt reward η clipped :=
    quittingSimonRationalPayoffAt_quittingPunishmentFloorClipAt
      reward η actual
  have hnoBadContinue : ∀ who,
      ¬IsQuittingRootBadContinueAt reward clipped β root who := by
    exact no_badContinue_supportPurifiedRoot_of_suppliedNoSure
      reward clipped root hβ.le hησ hrational hsupport hnoSure
  have hnotSure : ¬QuittingRootHasSureQuitter purified := by
    exact hnoSure clipped purified (hrational.mono hησ) (hsupport.mono hησ)
  have hquitLe : ∀ who,
      (purified who true).toReal ≤ (root who true).toReal := by
    exact supportPurifiedRoot_quitProbability_le_of_no_badContinue
      reward clipped β root hnoBadContinue
  have hρ : ρ ≤ quittingStationaryContinueMass purified := by
    exact rho_le_continueMass_supportPurifiedRoot_of_suppliedUniformSurvival
      reward clipped root hηρ hnear hrational hsupport huniform
  have hboundPos : 0 < α / (u * β) := div_pos hα (mul_pos hu hβ)
  have hdeleted : ∀ who,
      (root who true).toReal - (purified who true).toReal ≤ α / (u * β) := by
    classical
    intro who
    by_cases hbad : IsQuittingRootBadQuitAt reward clipped β root who
    · have hmul := hbadQuit who hbad
      have hsmall : (root who true).toReal < α / (u * β) := by
        have hdiv := (lt_div_iff₀ hβ).mpr hmul
        simpa only [div_div] using hdiv
      have hpure := quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
        reward clipped β root who hbad
      dsimp only [purified]
      rw [hpure]
      simpa using hsmall.le
    · have heq := quittingSupportPurifiedRoot_eq_self_of_not_bad
        reward clipped β root who hbad (hnoBadContinue who)
      dsimp only [purified]
      rw [heq, sub_self]
      exact hboundPos.le
  have hloss : quittingStationaryContinueMass purified -
      quittingStationaryContinueMass root ≤
        Fintype.card ι * α / (u * β) := by
    calc
      _ ≤ Fintype.card ι * (α / (u * β)) :=
        continueMass_supportPurifiedRoot_sub_le_card_mul
          reward clipped β (α / (u * β)) root hnoBadContinue hdeleted
      _ = Fintype.card ι * α / (u * β) := by ring
  exact ⟨hrational, hsupport, hclose, hnotSure, hquitLe, hρ, hloss⟩

/-! ## Exact first-crossing consequence -/

omit [DecidableEq ι] in
/-- A weak one-row survival lower bound is enough to trap a strict first
crossing in the interval `(θ * ρ / 6, θ / 3]`.  The strict lower endpoint
comes from the strict pre-crossing inequality; the crossing inequality itself
remains weak. -/
theorem quittingJointSurvivalWeight_firstCrossing_interval
    [Nonempty ι]
    (roots : ℕ → ι → PMF Bool) (T : ℕ)
    {θ ρ α β : ℝ}
    (hT : 0 < T) (hθ : 0 < θ) (hρ : 0 < ρ) (hβ : 0 < β)
    (hbefore : θ / 3 < quittingJointSurvivalWeight roots 0 (T - 1))
    (hcrossing : quittingJointSurvivalWeight roots 0 T ≤ θ / 3)
    (hbudget : α ≤ ρ * θ * β / (6 * Fintype.card ι))
    (hrow : ρ - Fintype.card ι * α /
        (quittingJointSurvivalWeight roots 0 (T - 1) * β) ≤
      quittingStationaryContinueMass (roots (T - 1))) :
    ρ / 2 < quittingStationaryContinueMass (roots (T - 1)) ∧
      θ * ρ / 6 < quittingJointSurvivalWeight roots 0 T ∧
        quittingJointSurvivalWeight roots 0 T ≤ θ / 3 := by
  let u := quittingJointSurvivalWeight roots 0 (T - 1)
  let n : ℝ := Fintype.card ι
  have hu : 0 < u := by
    dsimp only [u]
    linarith
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Fintype.card_pos
  have hdenom : 0 < 6 * n := mul_pos (by norm_num) hn
  have hscaled := (le_div_iff₀ hdenom).mp (by
    simpa only [n] using hbudget)
  have hθu : θ < 3 * u := by
    change θ / 3 < u at hbefore
    linarith
  have hρθ : ρ * θ < ρ * (3 * u) :=
    mul_lt_mul_of_pos_left hθu hρ
  have hρθβ : ρ * θ * β < ρ * (3 * u) * β :=
    mul_lt_mul_of_pos_right hρθ hβ
  have herror : n * α / (u * β) < ρ / 2 := by
    rw [div_lt_iff₀ (mul_pos hu hβ)]
    nlinarith
  have hcontinue : ρ / 2 <
      quittingStationaryContinueMass (roots (T - 1)) := by
    dsimp only [n, u] at herror
    linarith
  have hrecurrence : quittingJointSurvivalWeight roots 0 T =
      quittingJointSurvivalWeight roots 0 (T - 1) *
        quittingStationaryContinueMass (roots (T - 1)) := by
    have hrec := quittingJointSurvivalWeight_succ roots 0 (T - 1)
    rw [Nat.sub_add_cancel hT] at hrec
    simpa only [zero_add] using hrec
  have hproduct : (θ / 3) * (ρ / 2) <
      quittingJointSurvivalWeight roots 0 (T - 1) *
        quittingStationaryContinueMass (roots (T - 1)) :=
    mul_lt_mul hbefore hcontinue.le (div_pos hρ (by norm_num))
      (quittingJointSurvivalWeight_nonneg roots 0 (T - 1))
  refine ⟨hcontinue, ?_, hcrossing⟩
  rw [hrecurrence]
  nlinarith

/-- A floor-clipped purification certificate with the audited one-row loss
feeds the quantitative first-crossing lemma directly. -/
theorem QuittingFloorClippedPurificationCertificate.firstCrossing_interval
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (roots : ℕ → ι → PMF Bool)
    (purified : ι → PMF Bool) (T : ℕ)
    {d η θ ρ α β : ℝ}
    (certificate : QuittingFloorClippedPurificationCertificate reward tail
      d η ρ
        (Fintype.card ι * α /
          (quittingJointSurvivalWeight roots 0 (T - 1) * β))
        (roots (T - 1)) purified)
    (hT : 0 < T) (hθ : 0 < θ) (hρ : 0 < ρ) (hβ : 0 < β)
    (hbefore : θ / 3 < quittingJointSurvivalWeight roots 0 (T - 1))
    (hcrossing : quittingJointSurvivalWeight roots 0 T ≤ θ / 3)
    (hbudget : α ≤ ρ * θ * β / (6 * Fintype.card ι)) :
    ρ / 2 < quittingStationaryContinueMass (roots (T - 1)) ∧
      θ * ρ / 6 < quittingJointSurvivalWeight roots 0 T ∧
        quittingJointSurvivalWeight roots 0 T ≤ θ / 3 := by
  exact quittingJointSurvivalWeight_firstCrossing_interval roots T
    hT hθ hρ hβ hbefore hcrossing hbudget
      certificate.originalContinue_lower

end GameTheory
