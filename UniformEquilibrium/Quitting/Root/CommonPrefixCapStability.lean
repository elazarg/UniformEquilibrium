/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Unrestricted-cap stability behind a common finite prefix

A finite word of product roots acts on one player's unrestricted behavioral
best-response value by iterating scalar Bellman maps.  Behind a nonempty
word, the complete cap differs from the maximum of singleton cash-out and the
suffix cap by at most twice the reward bound times lost opponent survival.

The exact all-behavior one-root Bellman theorem supplies the first-stage pure
Quit/Continue reduction.  It retains the complete continuation supremum, so
Never and arbitrary behavioral deviations are included.  No Nash property,
source chronology, minimum, or equilibrium conclusion is assumed.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The scalar unrestricted-cap Bellman map at one prescribed product root.
Only the displayed player's suffix cap can affect the two pure endpoints. -/
private def quittingCommonPrefixCapStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (suffixCap : ℝ) : ℝ :=
  max
    (quittingRootQuitPayoff reward 0 root who)
    (quittingRootContinuePayoff reward
      (Function.update 0 who suffixCap) root who)

/-- Scalar Bellman action of a finite product-root word on one player's
suffix unrestricted cap. -/
def quittingFiniteRootWordCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (who : ι) (suffixCap : ℝ) : ℝ :=
  roots.foldr
    (fun root cap => quittingCommonPrefixCapStep reward root who cap)
    suffixCap

private theorem quittingRootContinuePayoff_zeroUpdate_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (first second : ℝ) :
    quittingRootContinuePayoff reward
        (Function.update (0 : Payoff ι) who first) root who -
        quittingRootContinuePayoff reward
          (Function.update (0 : Payoff ι) who second) root who =
      quittingRootOpponentContinueMass root who * (first - second) := by
  have hupdate : Function.update
      (Function.update (0 : Payoff ι) who second) who
      ((Function.update (0 : Payoff ι) who second) who + (first - second)) =
        Function.update (0 : Payoff ι) who first := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Function.update_of_ne hplayer]
  rw [← hupdate,
    quittingRootContinuePayoff_update_add reward
      (Function.update (0 : Payoff ι) who second) root who (first - second)]
  ring

private theorem abs_quittingCommonPrefixCapStep_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (first second : ℝ) :
    |quittingCommonPrefixCapStep reward root who first -
        quittingCommonPrefixCapStep reward root who second| ≤
      quittingRootOpponentContinueMass root who * |first - second| := by
  unfold quittingCommonPrefixCapStep
  rw [max_comm (quittingRootQuitPayoff reward 0 root who),
    max_comm (quittingRootQuitPayoff reward 0 root who)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [quittingRootContinuePayoff_zeroUpdate_sub_eq, abs_mul,
    abs_of_nonneg (quittingRootOpponentContinueMass_nonneg root who)]

private theorem abs_quittingCommonPrefixCapStep_sub_self_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (target M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htarget : |target| ≤ M)
    (hsingleton : reward (quittingSingletonTerminal who) who ≤ target) :
    |quittingCommonPrefixCapStep reward root who target - target| ≤
      2 * M * (1 - quittingRootOpponentContinueMass root who) := by
  have hquit :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward 0 root who M hreward
  have hcontinue :=
    QuittingAbsorptionPath.abs_quittingRootContinuePayoff_sub_tail_le_two_mul_opponentAbsorptionMass
      reward (Function.update 0 who target) root who M hreward (by simpa)
  have hmass : quittingRootOpponentAbsorptionMass root who =
      1 - quittingRootOpponentContinueMass root who := rfl
  rw [hmass] at hquit hcontinue
  simp only [Function.update_self] at hcontinue
  have herror : 0 ≤ 2 * M *
      (1 - quittingRootOpponentContinueMass root who) := by
    have hM : 0 ≤ M := (abs_nonneg target).trans htarget
    have hmassNonneg := quittingRootOpponentAbsorptionMass_nonneg root who
    rw [← hmass]
    positivity
  unfold quittingCommonPrefixCapStep
  calc
    |quittingCommonPrefixCapStep reward root who target - target| =
        |max
            (quittingRootQuitPayoff reward 0 root who)
            (quittingRootContinuePayoff reward
              (Function.update 0 who target) root who) -
          max (reward (quittingSingletonTerminal who) who) target| := by
            rw [max_eq_right hsingleton]
            rfl
    _ ≤ max
          |quittingRootQuitPayoff reward 0 root who -
            reward (quittingSingletonTerminal who) who|
          |quittingRootContinuePayoff reward
              (Function.update 0 who target) root who - target| :=
        abs_max_sub_max_le_max _ _ _ _
    _ ≤ 2 * M * (1 - quittingRootOpponentContinueMass root who) :=
      max_le hquit hcontinue

/-- A finite word transports a positive suffix-cap discrepancy by precisely
its player-deleted survival coefficient. Negative discrepancies require no
allowance in this one-sided bound. -/
theorem quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (who : ι) (first second : ℝ) :
    quittingFiniteRootWordCap reward roots who first -
        quittingFiniteRootWordCap reward roots who second ≤
      quittingLiteralRootStackOpponentSurvival roots who * max 0 (first - second) := by
  have hstep : ∀ root a b,
      quittingCommonPrefixCapStep reward root who a -
          quittingCommonPrefixCapStep reward root who b ≤
        quittingRootOpponentContinueMass root who * max 0 (a - b) := by
    intro root a b
    have hmass := quittingRootOpponentContinueMass_nonneg root who
    have hdiff := quittingRootContinuePayoff_zeroUpdate_sub_eq reward root who a b
    unfold quittingCommonPrefixCapStep
    have hnonneg : 0 ≤ quittingRootOpponentContinueMass root who * max 0 (a - b) :=
      mul_nonneg hmass (le_max_left _ _)
    apply sub_le_iff_le_add.mpr
    apply max_le
    · have hleft := le_max_left
        (quittingRootQuitPayoff reward 0 root who)
        (quittingRootContinuePayoff reward (Function.update 0 who b) root who)
      linarith
    · have hscaled := mul_le_mul_of_nonneg_left (le_max_right 0 (a - b)) hmass
      have hright := le_max_right
        (quittingRootQuitPayoff reward 0 root who)
        (quittingRootContinuePayoff reward (Function.update 0 who b) root who)
      linarith
  induction roots with
  | nil => simp [quittingFiniteRootWordCap, quittingLiteralRootStackOpponentSurvival]
  | cons root roots ih =>
      have hnonneg : 0 ≤ quittingLiteralRootStackOpponentSurvival roots who *
          max 0 (first - second) := mul_nonneg
        (quittingLiteralRootStackOpponentSurvival_nonneg roots who) (le_max_left _ _)
      have hmax := max_le hnonneg ih
      have hscaled := mul_le_mul_of_nonneg_left hmax
        (quittingRootOpponentContinueMass_nonneg root who)
      have h := (hstep root (quittingFiniteRootWordCap reward roots who first)
        (quittingFiniteRootWordCap reward roots who second)).trans hscaled
      simpa only [quittingFiniteRootWordCap, List.foldr_cons,
        quittingLiteralRootStackOpponentSurvival, List.map_cons, List.prod_cons,
        mul_assoc] using h

private theorem abs_quittingCommonPrefixCapStep_sub_max_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (suffixCap M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsuffix : |suffixCap| ≤ M) :
    |quittingCommonPrefixCapStep reward root who suffixCap -
        max (reward (quittingSingletonTerminal who) who) suffixCap| ≤
      2 * M * (1 - quittingRootOpponentContinueMass root who) := by
  have hquit :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward 0 root who M hreward
  have hcontinue :=
    QuittingAbsorptionPath.abs_quittingRootContinuePayoff_sub_tail_le_two_mul_opponentAbsorptionMass
      reward (Function.update 0 who suffixCap) root who M hreward (by simpa)
  change |max
      (quittingRootQuitPayoff reward 0 root who)
      (quittingRootContinuePayoff reward
        (Function.update 0 who suffixCap) root who) -
    max (reward (quittingSingletonTerminal who) who) suffixCap| ≤ _
  rw [show quittingRootOpponentAbsorptionMass root who =
      1 - quittingRootOpponentContinueMass root who from rfl] at hquit hcontinue
  simp only [Function.update_self] at hcontinue
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le hquit hcontinue)

/-- The complete behavioral cap behind a literal finite root word is exactly
the iterated scalar cap map applied to the suffix cap. -/
theorem quittingContinuationBestResponseValue_literalRootStack_eq_capFold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingLiteralRootStackProfile reward roots tail) who =
      quittingFiniteRootWordCap reward roots who
        (quittingContinuationBestResponseValue reward tail who) := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      rw [quittingLiteralRootStackProfile_cons,
        quittingContinuationBestResponseValue_rootThenContinuation_eq_max,
        ih]
      unfold quittingFiniteRootWordCap quittingCommonPrefixCapStep
      congr 1
      · exact quittingRootQuitPayoff_continuation_invariant reward _ 0 root who
      · unfold quittingRootContinuePayoff
        apply quittingRootExpectedPayoff_continuation_congr
        simp

private theorem abs_quittingFiniteRootWordCap_cons_sub_max_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (who : ι) (suffixCap M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsuffix : |suffixCap| ≤ M) :
    |quittingFiniteRootWordCap reward (root :: roots) who suffixCap -
        max (reward (quittingSingletonTerminal who) who) suffixCap| ≤
      2 * M *
        (1 - quittingLiteralRootStackOpponentSurvival (root :: roots) who) := by
  let target := max (reward (quittingSingletonTerminal who) who) suffixCap
  have hsingletonBound := hreward (quittingSingletonTerminal who) who
  have hM : 0 ≤ M := (abs_nonneg suffixCap).trans hsuffix
  have htarget : |target| ≤ M := by
    rw [abs_le]
    constructor
    · exact (neg_le_of_abs_le hsuffix).trans (le_max_right _ _)
    · exact max_le (le_of_abs_le hsingletonBound) (le_of_abs_le hsuffix)
  have hsingleton : reward (quittingSingletonTerminal who) who ≤ target :=
    le_max_left _ _
  induction roots generalizing root with
  | nil =>
      simpa [quittingFiniteRootWordCap,
        quittingLiteralRootStackOpponentSurvival, target] using
        abs_quittingCommonPrefixCapStep_sub_max_le
          reward root who suffixCap M hreward hsuffix
  | cons next roots ih =>
      have ihNext :
          |quittingCommonPrefixCapStep reward next who
                (quittingFiniteRootWordCap reward roots who suffixCap) - target| ≤
            2 * M *
              (1 - quittingRootOpponentContinueMass next who *
                quittingLiteralRootStackOpponentSurvival roots who) := by
        simpa only [quittingFiniteRootWordCap, List.foldr_cons,
          quittingLiteralRootStackOpponentSurvival, List.map_cons,
          List.prod_cons] using ih next
      have hstep := abs_quittingCommonPrefixCapStep_sub_le reward root who
        (quittingFiniteRootWordCap reward (next :: roots) who suffixCap)
        target
      have hfixed := abs_quittingCommonPrefixCapStep_sub_self_le
        reward root who target M hreward htarget hsingleton
      have hp := quittingRootOpponentContinueMass_nonneg root who
      have hscaled := mul_le_mul_of_nonneg_left ihNext hp
      simp only [quittingFiniteRootWordCap, List.foldr_cons,
        quittingLiteralRootStackOpponentSurvival, List.map_cons, List.prod_cons]
      calc
        |quittingCommonPrefixCapStep reward root who
              (quittingCommonPrefixCapStep reward next who
                (quittingFiniteRootWordCap reward roots who suffixCap)) - target| ≤
            |quittingCommonPrefixCapStep reward root who
                (quittingCommonPrefixCapStep reward next who
                  (quittingFiniteRootWordCap reward roots who suffixCap)) -
              quittingCommonPrefixCapStep reward root who target| +
            |quittingCommonPrefixCapStep reward root who target - target| := by
              exact abs_sub_le _ _ _
        _ ≤ quittingRootOpponentContinueMass root who *
              |quittingCommonPrefixCapStep reward next who
                  (quittingFiniteRootWordCap reward roots who suffixCap) - target| +
            2 * M * (1 - quittingRootOpponentContinueMass root who) :=
              add_le_add hstep hfixed
        _ ≤ quittingRootOpponentContinueMass root who *
              (2 * M *
                (1 - quittingRootOpponentContinueMass next who *
                  quittingLiteralRootStackOpponentSurvival roots who)) +
            2 * M * (1 - quittingRootOpponentContinueMass root who) :=
              by simpa only [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right hscaled
                  (2 * M * (1 - quittingRootOpponentContinueMass root who)))
        _ = 2 * M *
            (1 - quittingRootOpponentContinueMass root who *
              (quittingRootOpponentContinueMass next who *
                quittingLiteralRootStackOpponentSurvival roots who)) := by ring

/-- Sharp unrestricted-cap stability behind a nonempty common finite word.
The comparison is with the larger of singleton cash-out and the suffix's
complete behavioral cap. -/
theorem abs_quittingContinuationBestResponseValue_literalRootStack_sub_max_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward (root :: roots) tail) who -
        max (reward (quittingSingletonTerminal who) who)
          (quittingContinuationBestResponseValue reward tail who)| ≤
      2 * M *
        (1 - quittingLiteralRootStackOpponentSurvival (root :: roots) who) := by
  rw [quittingContinuationBestResponseValue_literalRootStack_eq_capFold]
  exact abs_quittingFiniteRootWordCap_cons_sub_max_le reward root roots who
    (quittingContinuationBestResponseValue reward tail who) M hreward
    (abs_quittingContinuationBestResponseValue_le reward tail who hreward)

/-- When the suffix cap already dominates singleton cash-out, the same sharp
estimate compares the prefixed unrestricted cap directly with the suffix
unrestricted cap. -/
theorem abs_quittingContinuationBestResponseValue_literalRootStack_sub_tail_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hmoat : reward (quittingSingletonTerminal who) who ≤
      quittingContinuationBestResponseValue reward tail who) :
    |quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward (root :: roots) tail) who -
        quittingContinuationBestResponseValue reward tail who| ≤
      2 * M *
        (1 - quittingLiteralRootStackOpponentSurvival (root :: roots) who) := by
  simpa only [max_eq_right hmoat] using
    abs_quittingContinuationBestResponseValue_literalRootStack_sub_max_le
      reward root roots tail who hreward

/-- Two arbitrary suffix caps behind the same finite word contract by the
word's opponent-deleted survival.  No reward bound is needed. -/
theorem abs_quittingContinuationBestResponseValue_literalRootStack_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    |quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward roots first) who -
        quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward roots second) who| ≤
      quittingLiteralRootStackOpponentSurvival roots who *
        |quittingContinuationBestResponseValue reward first who -
          quittingContinuationBestResponseValue reward second who| := by
  rw [quittingContinuationBestResponseValue_literalRootStack_eq_capFold,
    quittingContinuationBestResponseValue_literalRootStack_eq_capFold]
  induction roots with
  | nil => simp [quittingFiniteRootWordCap,
      quittingLiteralRootStackOpponentSurvival]
  | cons root roots ih =>
      simp only [quittingFiniteRootWordCap, List.foldr_cons,
        quittingLiteralRootStackOpponentSurvival, List.map_cons, List.prod_cons]
      have hscaled := mul_le_mul_of_nonneg_left ih
        (quittingRootOpponentContinueMass_nonneg root who)
      exact (abs_quittingCommonPrefixCapStep_sub_le reward root who _ _).trans
        (by simpa only [mul_assoc, quittingFiniteRootWordCap,
            quittingLiteralRootStackOpponentSurvival] using hscaled)

/-- Vanishing opponent-prefix absorption transports a convergent suffix cap
through any nonempty sequence of literal root words, provided the limiting
suffix cap strictly dominates singleton cash-out. -/
theorem tendsto_quittingContinuationBestResponseValue_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℕ → ι → PMF Bool)
    (roots : ℕ → List (ι → PMF Bool))
    (tail : ℕ → (quittingGame reward).BehaviorProfile)
    (who : ι) (limit : ℝ)
    (hsurvival : Tendsto (fun n =>
      quittingLiteralRootStackOpponentSurvival (root n :: roots n) who)
      atTop (nhds 1))
    (htail : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (tail n) who)
      atTop (nhds limit))
    (hmoat : reward (quittingSingletonTerminal who) who < limit) :
    Tendsto (fun n => quittingContinuationBestResponseValue reward
      (quittingLiteralRootStackProfile reward (root n :: roots n) (tail n)) who)
      atTop (nhds limit) := by
  obtain ⟨M, _hM, hreward⟩ := exists_quittingRewardBound reward
  have hmax : Tendsto (fun n =>
      max (reward (quittingSingletonTerminal who) who)
        (quittingContinuationBestResponseValue reward (tail n) who))
      atTop (nhds limit) := by
    have heventually : ∀ᶠ n in atTop,
        reward (quittingSingletonTerminal who) who <
          quittingContinuationBestResponseValue reward (tail n) who :=
      (tendsto_order.1 htail).1 _ hmoat
    exact htail.congr' <| heventually.mono fun n hn =>
      (max_eq_right hn.le).symm
  have herror : Tendsto (fun n => 2 * M *
      (1 - quittingLiteralRootStackOpponentSurvival
        (root n :: roots n) who)) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hsurvival) using 1
    ring_nf
  have habs : Tendsto (fun n =>
      |quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward (root n :: roots n) (tail n))
          who -
        max (reward (quittingSingletonTerminal who) who)
          (quittingContinuationBestResponseValue reward (tail n) who)|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => abs_nonneg _
    · exact Eventually.of_forall fun n =>
        abs_quittingContinuationBestResponseValue_literalRootStack_sub_max_le
          reward (root n) (roots n) (tail n) who hreward
    · exact herror
  have hdifference : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward (root n :: roots n) (tail n))
          who -
        max (reward (quittingSingletonTerminal who) who)
          (quittingContinuationBestResponseValue reward (tail n) who))
      atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  convert hdifference.add hmax using 1 <;> simp

/-- Joint survival tending to one is sufficient for the same cap transport,
because every player-deleted survival tends to one. -/
theorem tendsto_quittingContinuationBestResponseValue_literalRootStack_of_joint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℕ → ι → PMF Bool)
    (roots : ℕ → List (ι → PMF Bool))
    (tail : ℕ → (quittingGame reward).BehaviorProfile)
    (who : ι) (limit : ℝ)
    (hsurvival : Tendsto (fun n =>
      quittingLiteralRootStackJointSurvival (root n :: roots n))
      atTop (nhds 1))
    (htail : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (tail n) who)
      atTop (nhds limit))
    (hmoat : reward (quittingSingletonTerminal who) who < limit) :
    Tendsto (fun n => quittingContinuationBestResponseValue reward
      (quittingLiteralRootStackProfile reward (root n :: roots n) (tail n)) who)
      atTop (nhds limit) := by
  exact tendsto_quittingContinuationBestResponseValue_literalRootStack
    reward root roots tail who limit
      (tendsto_quittingLiteralRootStackOpponentSurvival_one
        (fun n => root n :: roots n) who hsurvival)
      htail hmoat

end GameTheory
