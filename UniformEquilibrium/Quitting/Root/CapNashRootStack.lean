/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack
import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Terminal.TerminalDebtPrefixDescent

/-! # Cap--Nash root stacks

This module contains the root-level foundation for finite literal stacks whose
roots are exact Nash against the complete unilateral cap of their executable
suffix.  The defining one-step cancellation and its finite playerwise fold are
semantic identities; debt-infimum and near-minimum chronology arguments remain
in the diagnostics layer.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Prefixing a semantic pair by an exact Nash root against its envelope
scales each debt coordinate by joint Continue mass. -/
theorem quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebt pair who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [hquit, hcontinue,
    ← quittingRootSuccessorPayoff_eq_max_of_isZeroNash
      reward pair.2 root who hnash,
    quittingRootSuccessorPayoff_sub_eq_continueMass_mul]

/-- Exact Nash against the envelope makes the prefixed envelope the exact
Bellman successor of the original envelope. -/
theorem quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    (quittingTerminalSemanticPrefix reward root pair).2 =
      quittingRootSuccessorPayoff reward pair.2 root := by
  funext who
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  unfold quittingTerminalSemanticPrefix
  dsimp only
  rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash
    reward pair.2 root who hnash, hquit, hcontinue]

/-- Literal specialization of exact cap--Nash debt scaling. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      quittingStationaryContinueMass root *
        quittingTerminalDeviationDebt reward continuation who := by
  have hpair := quittingTerminalSemanticPair_rootThenContinuation
    reward root continuation
  have hsemantic :=
    quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) (quittingTerminalSemanticPair reward continuation)
      root who hnash
  rw [← hpair] at hsemantic
  exact hsemantic

/-- Total literal debt obeys the same exact cap--Nash scaling. -/
theorem quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (hnash : IsεQuittingRootNash reward
      (fun player =>
        quittingContinuationBestResponseValue reward continuation player)
      0 root) :
    quittingTerminalDebtSum reward
        (quittingRootThenContinuationProfile reward root continuation) =
      quittingStationaryContinueMass root *
        quittingTerminalDebtSum reward continuation := by
  unfold quittingTerminalDebtSum
  simp_rw [quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
    (reward := reward) root continuation _ hnash]
  rw [Finset.mul_sum]

/-- Every root is exact Nash against the unilateral cap of the remaining
executable suffix. -/
def IsQuittingCapNashRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (ι → PMF Bool) → (quittingGame reward).BehaviorProfile → Prop
  | [], _ => True
  | root :: roots, terminal =>
      IsεQuittingRootNash reward
        (fun player => quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward roots terminal) player)
        0 root ∧
      IsQuittingCapNashRootStack reward roots terminal

@[simp] theorem isQuittingCapNashRootStack_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    IsQuittingCapNashRootStack reward [] terminal := trivial

theorem isQuittingCapNashRootStack_cons_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    IsQuittingCapNashRootStack reward (root :: roots) terminal ↔
      IsεQuittingRootNash reward
        (fun player => quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward roots terminal) player)
        0 root ∧ IsQuittingCapNashRootStack reward roots terminal := by
  rfl

/-- Dropping a chronological prefix preserves the cap--Nash stack property. -/
theorem IsQuittingCapNashRootStack.drop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hstack : IsQuittingCapNashRootStack reward roots terminal)
    (count : ℕ) :
    IsQuittingCapNashRootStack reward (roots.drop count) terminal := by
  induction roots generalizing count with
  | nil => simp
  | cons root roots ih =>
      cases count with
      | zero => simpa using hstack
      | succ count =>
          rw [isQuittingCapNashRootStack_cons_iff] at hstack
          simpa using ih hstack.2 count

/-- Exact cap--Nash stacks exist over every executable terminal continuation. -/
theorem exists_quittingCapNashRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) (depth : ℕ) :
    ∃ roots : List (ι → PMF Bool), roots.length = depth ∧
      IsQuittingCapNashRootStack reward roots terminal := by
  induction depth with
  | zero => exact ⟨[], rfl, trivial⟩
  | succ depth ih =>
      obtain ⟨roots, hlength, hstack⟩ := ih
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash
        (reward := reward)
        (fun player => quittingContinuationBestResponseValue reward suffix player)
      refine ⟨root :: roots, by simp [hlength], ?_⟩
      exact ⟨by simpa [suffix] using hnash, hstack⟩

/-- Joint survival of a finite root word. -/
def quittingCapNashStackContinueProduct
    (roots : List (ι → PMF Bool)) : ℝ :=
  quittingLiteralRootStackJointSurvival roots

omit [DecidableEq ι] in
@[simp] theorem quittingCapNashStackContinueProduct_nil :
    quittingCapNashStackContinueProduct ([] : List (ι → PMF Bool)) = 1 := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingCapNashStackContinueProduct_cons
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool)) :
    quittingCapNashStackContinueProduct (root :: roots) =
      quittingStationaryContinueMass root *
        quittingCapNashStackContinueProduct roots := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingCapNashStackContinueProduct_append
    (first second : List (ι → PMF Bool)) :
    quittingCapNashStackContinueProduct (first ++ second) =
      quittingCapNashStackContinueProduct first *
        quittingCapNashStackContinueProduct second :=
  quittingLiteralRootStackJointSurvival_append first second

omit [DecidableEq ι] in
theorem quittingCapNashStackContinueProduct_nonneg
    (roots : List (ι → PMF Bool)) :
    0 ≤ quittingCapNashStackContinueProduct roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingCapNashStackContinueProduct_cons]
      exact mul_nonneg (quittingStationaryContinueMass_nonneg root) ih

omit [DecidableEq ι] in
theorem quittingCapNashStackContinueProduct_le_one
    (roots : List (ι → PMF Bool)) :
    quittingCapNashStackContinueProduct roots ≤ 1 := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingCapNashStackContinueProduct_cons]
      have hrootNonneg := quittingStationaryContinueMass_nonneg root
      have hrootLe := quittingStationaryContinueMass_le_one root
      have htailNonneg := quittingCapNashStackContinueProduct_nonneg roots
      nlinarith [mul_nonneg hrootNonneg htailNonneg,
        mul_nonneg (sub_nonneg.mpr hrootLe) htailNonneg]

/-- Exact folded playerwise debt scaling along a cap--Nash root stack. -/
theorem quittingTerminalDeviationDebt_capNashRootStack_eq
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward roots terminal) who =
      quittingCapNashStackContinueProduct roots *
        quittingTerminalDeviationDebt reward terminal who := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [isQuittingCapNashRootStack_cons_iff] at hstack
      rw [quittingLiteralRootStackProfile_cons,
        quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
          (reward := reward) root
          (quittingLiteralRootStackProfile reward roots terminal) who
          hstack.1,
        ih hstack.2]
      rw [quittingCapNashStackContinueProduct_cons]
      ring

/-- Exact folded total-debt scaling along a cap--Nash root stack. -/
theorem quittingTerminalDebtSum_capNashRootStack_eq
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hstack : IsQuittingCapNashRootStack reward roots terminal) :
    quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward roots terminal) =
      quittingCapNashStackContinueProduct roots *
        quittingTerminalDebtSum reward terminal := by
  unfold quittingTerminalDebtSum
  simp_rw [quittingTerminalDeviationDebt_capNashRootStack_eq
    (reward := reward) roots terminal _ hstack]
  rw [Finset.mul_sum]

omit [DecidableEq ι] in
/-- The cap--Nash stack product is the canonical literal-word joint survival. -/
theorem quittingCapNashStackContinueProduct_eq_literalRootStackJointSurvival
    (roots : List (ι → PMF Bool)) :
    quittingCapNashStackContinueProduct roots =
      quittingLiteralRootStackJointSurvival roots := rfl

end GameTheory
