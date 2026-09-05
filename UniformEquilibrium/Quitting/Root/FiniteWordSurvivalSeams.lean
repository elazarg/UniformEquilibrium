/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Root.FiniteWordSemanticSplice

/-! # Exact-chain and live-clock specializations of finite-word splicing -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An exact Nash chain has zero algebraic prefix debt. Each root is tested
at the payoff of its literal suffix, not at a reselected continuation. -/
theorem quittingFiniteRootWordSemanticPrefix_diagonal_of_exactChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : Payoff ι)
    (hchain : ∀ before root after, roots = before ++ root :: after →
      IsεQuittingRootNash reward (quittingFiniteRootWordPayoff reward after tail) 0 root) :
    quittingFiniteRootWordSemanticPrefix reward roots (tail, tail) =
      (quittingFiniteRootWordPayoff reward roots tail,
        quittingFiniteRootWordPayoff reward roots tail) := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      have hrest : ∀ before next after, roots = before ++ next :: after →
          IsεQuittingRootNash reward (quittingFiniteRootWordPayoff reward after tail) 0 next := by
        intro before next after heq
        exact hchain (root :: before) next after (by simp [heq])
      rw [quittingFiniteRootWordSemanticPrefix_eq_foldr, List.foldr_cons,
        ← quittingFiniteRootWordSemanticPrefix_eq_foldr, ih hrest,
        quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash reward _ root
          (hchain [] root roots rfl)]
      rfl

/-- A positive joint floor turns the transmitted payoff seam and positive
cap seam into vanishing actual tail debt, even when the references vary. -/
theorem tailDebt_tendsto_zero_of_jointFloor_seams
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (reference : ℕ → Payoff ι) (who : ι) {floor : ℝ} (hfloor : 0 < floor)
    (hjoint : ∀ index, floor ≤ quittingLiteralRootStackJointSurvival (roots index))
    (hpayoff : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index) *
      |quittingTerminalPayoff reward (tails index) who - reference index who|)
      atTop (nhds 0))
    (hcap : Tendsto (fun index ↦ quittingLiteralRootStackOpponentSurvival (roots index) who *
      max 0 (quittingContinuationBestResponseValue reward (tails index) who -
        reference index who)) atTop (nhds 0)) :
    Tendsto (fun index ↦ quittingTerminalDeviationDebt reward (tails index) who)
      atTop (nhds 0) := by
  have hlimit := (hcap.add hpayoff).div_const floor
  simp only [add_zero, zero_div] at hlimit
  apply squeeze_zero
    (fun index ↦ quittingTerminalDeviationDebt_nonneg reward (tails index) who) _ hlimit
  intro index
  apply (le_div_iff₀ hfloor).2
  have hbeta := (hjoint index).trans
    (quittingLiteralRootStackJointSurvival_le_opponentSurvival (roots index) who)
  have hc := mul_le_mul_of_nonneg_right hbeta
    (le_max_left 0 (quittingContinuationBestResponseValue reward (tails index) who -
      reference index who))
  have hp := mul_le_mul_of_nonneg_right (hjoint index)
    (abs_nonneg (quittingTerminalPayoff reward (tails index) who - reference index who))
  have hs := le_max_right 0 (quittingContinuationBestResponseValue reward (tails index) who -
    reference index who)
  have ha := neg_abs_le (quittingTerminalPayoff reward (tails index) who - reference index who)
  unfold quittingTerminalDeviationDebt
  nlinarith

/-- Under a positive joint floor, both coordinates approach the varying
diagonal reference; no convergence of that reference is presumed. -/
theorem tailReferenceSeams_tendsto_zero_of_jointFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (reference : ℕ → Payoff ι) (who : ι) {floor : ℝ} (hfloor : 0 < floor)
    (hjoint : ∀ index, floor ≤ quittingLiteralRootStackJointSurvival (roots index))
    (hpayoff : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index) *
      |quittingTerminalPayoff reward (tails index) who - reference index who|)
      atTop (nhds 0))
    (hcap : Tendsto (fun index ↦ quittingLiteralRootStackOpponentSurvival (roots index) who *
      max 0 (quittingContinuationBestResponseValue reward (tails index) who -
        reference index who)) atTop (nhds 0)) :
    Tendsto (fun index ↦ |quittingTerminalPayoff reward (tails index) who - reference index who|)
      atTop (nhds 0) ∧
    Tendsto (fun index ↦ |quittingContinuationBestResponseValue reward (tails index) who -
      reference index who|) atTop (nhds 0) := by
  have habs : Tendsto
      (fun index ↦ |quittingTerminalPayoff reward (tails index) who - reference index who|)
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ ↦ abs_nonneg _) _ (by simpa using hpayoff.div_const floor)
    intro index
    apply (le_div_iff₀ hfloor).2
    nlinarith [mul_le_mul_of_nonneg_right (hjoint index)
      (abs_nonneg (quittingTerminalPayoff reward (tails index) who - reference index who))]
  have hdiff := (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have hdebt := tailDebt_tendsto_zero_of_jointFloor_seams
    reward roots tails reference who hfloor hjoint hpayoff hcap
  refine ⟨habs, ?_⟩
  have hsum := hdebt.add hdiff
  simp only [zero_add] at hsum
  have hcapDiff : Tendsto (fun index ↦ quittingContinuationBestResponseValue reward
      (tails index) who - reference index who) atTop (nhds 0) := by
    convert hsum using 1
    funext index
    unfold quittingTerminalDeviationDebt
    ring
  simpa using hcapDiff.abs

/-- A vanishing deleted clock erases every bounded positive cap seam. This
does not assert anything about the independent algebraic prefix debt. -/
theorem capSeam_tendsto_zero_of_deletedClock_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (reference : ℕ → Payoff ι) (who : ι) (bound : ℝ)
    (hbound : ∀ index, max 0 (quittingContinuationBestResponseValue reward (tails index) who -
      reference index who) ≤ bound)
    (hclock : Tendsto (fun index ↦ quittingLiteralRootStackOpponentSurvival (roots index) who)
      atTop (nhds 0)) :
    Tendsto (fun index ↦ quittingLiteralRootStackOpponentSurvival (roots index) who *
      max 0 (quittingContinuationBestResponseValue reward (tails index) who - reference index who))
      atTop (nhds 0) := by
  apply squeeze_zero
    (fun index ↦ mul_nonneg (quittingLiteralRootStackOpponentSurvival_nonneg _ _)
      (le_max_left _ _))
    (fun index ↦ mul_le_mul_of_nonneg_left (hbound index)
      (quittingLiteralRootStackOpponentSurvival_nonneg _ _))
  simpa using hclock.mul_const bound

omit [DecidableEq ι] in
/-- A vanishing joint clock erases every bounded prescribed-payoff seam. -/
theorem payoffSeam_tendsto_zero_of_jointClock_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (reference : ℕ → Payoff ι) (who : ι) (bound : ℝ)
    (hbound : ∀ index, |quittingTerminalPayoff reward (tails index) who - reference index who| ≤
      bound)
    (hclock : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0)) :
    Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index) *
      |quittingTerminalPayoff reward (tails index) who - reference index who|)
      atTop (nhds 0) := by
  apply squeeze_zero
    (fun index ↦ mul_nonneg (quittingLiteralRootStackJointSurvival_nonneg _) (abs_nonneg _))
    (fun index ↦ mul_le_mul_of_nonneg_left (hbound index)
      (quittingLiteralRootStackJointSurvival_nonneg _))
  simpa using hclock.mul_const bound

end GameTheory
