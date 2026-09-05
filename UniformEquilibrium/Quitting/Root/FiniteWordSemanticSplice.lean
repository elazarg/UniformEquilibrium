/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Root.CommonPrefixCapStability
import UniformEquilibrium.Quitting.Root.LiteralPrefixDeviationTransport
import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier

/-! # Actual finite-word tail extraction and semantic splicing

Joint survival transports prescribed payoff differences. Player-deleted
survival transports the positive part of a suffix-cap discrepancy. The two
coefficients remain distinct, and every behavioral tail is unrestricted.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Algebraic prescribed payoff of a finite chronological word. -/
def quittingFiniteRootWordPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : Payoff ι) : Payoff ι :=
  roots.foldr (fun root value ↦ quittingRootSuccessorPayoff reward value root) tail

/-- The full semantic word action, including algebraic reference pairs which
are not assumed executable. -/
def quittingFiniteRootWordSemanticPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (quittingFiniteRootWordPayoff reward roots pair.1,
    fun who ↦ quittingFiniteRootWordCap reward roots who (pair.2 who))

/-- The separated coordinate folds are exactly the native semantic prefix
fold, on every algebraic pair without executability assumptions. -/
theorem quittingFiniteRootWordSemanticPrefix_eq_foldr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (pair : QuittingTerminalSemanticPair ι) :
    quittingFiniteRootWordSemanticPrefix reward roots pair =
      roots.foldr (quittingTerminalSemanticPrefix reward) pair := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      rw [List.foldr_cons, ← ih]
      apply Prod.ext
      · rfl
      · funext who
        change max (quittingRootQuitPayoff reward 0 root who)
            (quittingRootContinuePayoff reward (Function.update 0 who _) root who) =
          max (quittingRootQuitPayoff reward _ root who)
            (quittingRootContinuePayoff reward (Function.update _ who _) root who)
        congr 1
        · exact quittingRootQuitPayoff_continuation_invariant reward 0 _ root who
        · unfold quittingRootContinuePayoff
          apply quittingRootExpectedPayoff_continuation_congr
          simp [quittingFiniteRootWordSemanticPrefix, quittingFiniteRootWordCap]

omit [DecidableEq ι] in
theorem quittingTerminalPayoff_literalRootStack_eq_wordPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward (quittingLiteralRootStackProfile reward roots tail) =
      quittingFiniteRootWordPayoff reward roots (quittingTerminalPayoff reward tail) := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      funext who
      rw [quittingLiteralRootStackProfile_cons, quittingTerminalPayoff_rootThenContinuation_eq]
      change quittingRootSuccessorPayoff reward _ root who = _
      rw [ih]
      rfl

theorem quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward (quittingLiteralRootStackProfile reward roots tail) =
      quittingFiniteRootWordSemanticPrefix reward roots
        (quittingTerminalSemanticPair reward tail) := by
  apply Prod.ext
  · exact quittingTerminalPayoff_literalRootStack_eq_wordPayoff reward roots tail
  · funext who
    exact quittingContinuationBestResponseValue_literalRootStack_eq_capFold reward roots tail who

omit [DecidableEq ι] in
/-- Algebraic suffix-payoff differences are multiplied by joint survival. -/
theorem quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (first second : Payoff ι) (who : ι) :
    quittingFiniteRootWordPayoff reward roots first who -
        quittingFiniteRootWordPayoff reward roots second who =
      quittingLiteralRootStackJointSurvival roots * (first who - second who) := by
  induction roots with
  | nil => simp [quittingFiniteRootWordPayoff, quittingLiteralRootStackJointSurvival]
  | cons root roots ih =>
      simp only [quittingFiniteRootWordPayoff, List.foldr_cons,
        quittingRootSuccessorPayoff, quittingRootExpectedPayoff_eq_absorbingContribution_add]
      simp only [quittingFiniteRootWordPayoff] at ih
      unfold quittingLiteralRootStackJointSurvival at ih
      simp only [quittingLiteralRootStackJointSurvival, List.map_cons, List.prod_cons]
      linear_combination quittingStationaryContinueMass root * ih

/-- Positive joint reach extracts the actual arbitrary behavioral tail with
the sharp divided Nash error. -/
theorem isAsymptoticNash_tail_of_literalRootStack_joint_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : (quittingGame reward).BehaviorProfile)
    (error : ℝ) (hjoint : 0 < quittingLiteralRootStackJointSurvival roots)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      error (quittingLiteralRootStackProfile reward roots tail)) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (error / quittingLiteralRootStackJointSurvival roots) tail := by
  intro who deviation
  have h := hnash who (quittingCopyLiteralRootStackThenDeviation reward roots who deviation)
  have hid := quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq
    reward roots tail who deviation
  have hgain : quittingTerminalPayoff reward (Function.update tail who deviation) who -
      quittingTerminalPayoff reward tail who ≤
        error / quittingLiteralRootStackJointSurvival roots :=
    (le_div_iff₀ hjoint).2 (by nlinarith)
  linarith

private theorem terminalDebt_le_nashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) (error : ℝ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error tail) (who : ι) :
    quittingTerminalDeviationDebt reward tail who ≤ error := by
  have hcap : quittingContinuationBestResponseValue reward tail who ≤
      quittingTerminalPayoff reward tail who + error := by
    letI : Nonempty ((quittingGame reward).BehaviorStrategy who) := ⟨tail who⟩
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨deviation, rfl⟩
    exact hnash who deviation
  exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hcap)

/-- Vanishing divided error yields a diagonal limit along a strict
subsequence of the actual tails, and that fixed limit is a uniform payoff. -/
theorem exists_diagonal_tail_limit_of_literalRootStack_nash_ratio [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (error : ℕ → ℝ)
    (hjoint : ∀ index, 0 < quittingLiteralRootStackJointSurvival (roots index))
    (hnash : ∀ index, (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (error index)
      (quittingLiteralRootStackProfile reward (roots index) (tails index)))
    (hratio : Tendsto (fun index ↦ error index /
      quittingLiteralRootStackJointSurvival (roots index)) atTop (nhds 0)) :
    ∃ target : Payoff ι, ∃ select : ℕ → ℕ, StrictMono select ∧
      Tendsto (fun index ↦ quittingTerminalSemanticPair reward (tails (select index)))
        atTop (nhds (target, target)) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  have htail := fun index ↦ isAsymptoticNash_tail_of_literalRootStack_joint_pos
    reward (roots index) (tails index) (error index) (hjoint index) (hnash index)
  obtain ⟨pair, hpair, select, hselect, hlimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
      (fun index ↦ subset_closure (Set.mem_range_self (tails index)))
  have hdiag : pair.2 = pair.1 := by
    funext who
    have hzero : Tendsto (fun index ↦ quittingTerminalDeviationDebt reward (tails index) who)
        atTop (nhds 0) :=
      squeeze_zero (fun index ↦ quittingTerminalDeviationDebt_nonneg reward (tails index) who)
        (fun index ↦ terminalDebt_le_nashError reward (tails index) _ (htail index) who) hratio
    have hcoordinate :=
      (((continuous_apply who).comp continuous_snd).tendsto pair).comp hlimit |>.sub
        ((((continuous_apply who).comp continuous_fst).tendsto pair).comp hlimit)
    have hid := tendsto_nhds_unique hcoordinate (hzero.comp hselect.tendsto_atTop)
    exact sub_eq_zero.mp hid
  have hp : pair = (pair.1, pair.1) := Prod.ext rfl hdiag
  refine ⟨pair.1, select, hselect, ?_, ?_⟩
  · exact hp ▸ hlimit
  · apply isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
    exact hp ▸ hpair

/-- Complete debt of the actual splice is bounded by the algebraic prefix
debt plus the transmitted positive cap seam and absolute payoff seam. -/
theorem literalRootStack_debt_le_referenceDebt_add_transmittedSeams
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : (quittingGame reward).BehaviorProfile)
    (reference : Payoff ι) (who : ι) :
    quittingTerminalDeviationDebt reward (quittingLiteralRootStackProfile reward roots tail) who ≤
      quittingTerminalSemanticDebt
          (quittingFiniteRootWordSemanticPrefix reward roots (reference, reference)) who +
        quittingLiteralRootStackOpponentSurvival roots who *
          max 0 (quittingContinuationBestResponseValue reward tail who - reference who) +
        quittingLiteralRootStackJointSurvival roots *
          |quittingTerminalPayoff reward tail who - reference who| := by
  have hcap := quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart
    reward roots who (quittingContinuationBestResponseValue reward tail who) (reference who)
  rw [← quittingContinuationBestResponseValue_literalRootStack_eq_capFold reward roots tail who]
    at hcap
  have hpayoff := quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul
    reward roots (quittingTerminalPayoff reward tail) reference who
  rw [← quittingTerminalPayoff_literalRootStack_eq_wordPayoff reward roots tail] at hpayoff
  have habs := neg_abs_le (quittingTerminalPayoff reward tail who - reference who)
  have hscaled := mul_le_mul_of_nonneg_left habs
    (quittingLiteralRootStackJointSurvival_nonneg roots)
  unfold quittingTerminalDeviationDebt quittingTerminalSemanticDebt
    quittingFiniteRootWordSemanticPrefix
  dsimp only
  nlinarith

/-- Growing literal words compile a fixed uniform target when their reference
debt and the two distinct transmitted seams vanish. -/
theorem growingWord_referenceSeams_completion [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (reference : ℕ → Payoff ι) (target : Payoff ι)
    (htarget : Tendsto (fun index ↦
      quittingFiniteRootWordPayoff reward (roots index) (reference index)) atTop (nhds target))
    (hdebt : ∀ who, Tendsto (fun index ↦ quittingTerminalSemanticDebt
      (quittingFiniteRootWordSemanticPrefix reward (roots index)
        (reference index, reference index)) who) atTop (nhds 0))
    (hpayoff : ∀ who, Tendsto (fun index ↦
      quittingLiteralRootStackJointSurvival (roots index) *
        |quittingTerminalPayoff reward (tails index) who - reference index who|)
      atTop (nhds 0))
    (hcap : ∀ who, Tendsto (fun index ↦
      quittingLiteralRootStackOpponentSurvival (roots index) who *
        max 0 (quittingContinuationBestResponseValue reward (tails index) who -
          reference index who)) atTop (nhds 0)) :
    Tendsto (fun index ↦ quittingTerminalPayoff reward
      (quittingLiteralRootStackProfile reward (roots index) (tails index)))
      atTop (nhds target) ∧
    Tendsto (fun index ↦ quittingTerminalExploitability reward
      (quittingLiteralRootStackProfile reward (roots index) (tails index)))
      atTop (nhds 0) ∧
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  let profiles := fun index ↦ quittingLiteralRootStackProfile reward (roots index) (tails index)
  have hdebtZero : ∀ who, Tendsto (fun index ↦
      quittingTerminalDeviationDebt reward (profiles index) who) atTop (nhds 0) := by
    intro who
    apply squeeze_zero
      (fun index ↦ quittingTerminalDeviationDebt_nonneg reward (profiles index) who)
      (fun index ↦ literalRootStack_debt_le_referenceDebt_add_transmittedSeams
        reward (roots index) (tails index) (reference index) who)
    simpa using ((hdebt who).add (hcap who)).add (hpayoff who)
  let error := fun index ↦ ∑ who, quittingTerminalDeviationDebt reward (profiles index) who
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using tendsto_finsetSum Finset.univ fun who _ ↦ hdebtZero who
  have hnash : ∀ index, (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (error index) (profiles index) := by
    intro index who deviation
    have hgain := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (profiles index) who deviation
    have hsingle : quittingTerminalDeviationDebt reward (profiles index) who ≤ error index :=
      Finset.single_le_sum (fun player _ ↦
        quittingTerminalDeviationDebt_nonneg reward (profiles index) player) (Finset.mem_univ who)
    unfold quittingTerminalDeviationDebt at hsingle
    linarith
  have hactual : Tendsto (fun index ↦ quittingTerminalPayoff reward (profiles index))
      atTop (nhds target) := by
    apply tendsto_pi_nhds.2
    intro who
    have hdiff : Tendsto (fun index ↦ quittingTerminalPayoff reward (profiles index) who -
        quittingFiniteRootWordPayoff reward (roots index) (reference index) who)
        atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (by simpa using (hpayoff who).neg) (hpayoff who)
      · intro index
        dsimp [profiles]
        rw [quittingTerminalPayoff_literalRootStack_eq_wordPayoff,
          quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul]
        nlinarith [neg_abs_le (quittingTerminalPayoff reward (tails index) who -
          reference index who), quittingLiteralRootStackJointSurvival_nonneg (roots index)]
      intro index
      dsimp [profiles]
      rw [quittingTerminalPayoff_literalRootStack_eq_wordPayoff,
        quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul]
      exact mul_le_mul_of_nonneg_left (le_abs_self _)
        (quittingLiteralRootStackJointSurvival_nonneg (roots index))
    have h := hdiff.add (((continuous_apply who).tendsto target).comp htarget)
    simpa using h
  refine ⟨hactual, ?_, quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward target error profiles herror (Frequently.of_forall hnash) hactual⟩
  exact squeeze_zero (fun index ↦ quittingTerminalExploitability_nonneg reward (profiles index))
    (fun index ↦ quittingTerminalExploitability_le_of_isεAsymptoticNash
      reward (profiles index) (Finset.sum_nonneg fun who _ ↦
        quittingTerminalDeviationDebt_nonneg reward (profiles index) who) (hnash index)) herror

end GameTheory
