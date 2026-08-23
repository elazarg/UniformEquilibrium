/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Terminal semantics and a common witness are not splice-compositional

Two literal three-player profiles below have the same complete terminal
semantic pair, the same first-stage joint survival, and the same exact pure
stopping-time witness for player zero.  Their player-zero-deleted survival
weights differ.  Prefixing the same continuation therefore gives different
best-response values.  The missing compositional datum is the labelled
deleted clock, not another terminal payoff coordinate.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

namespace QuittingCommonWitnessNoncompositionality

abbrev Player := Fin 3

abbrev owner : Player := 0
abbrev blocker : Player := 1
abbrev successor : Player := 2

/-- Only player zero is paid.  Solo stopping by zero or one pays one, their
collision pays zero, and a zero--two collision pays two. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who =>
    if who = owner then
      if terminal.val = {owner} then 1
      else if terminal.val = {blocker} then 1
      else if terminal.val = {owner, successor} then 2
      else 0
    else 0

/-- A root at which exactly `marked` has quitting probability `1-s`. -/
def root (marked : Player) (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    Player -> PMF Bool := fun who =>
  if who = marked then
    quittingHazardCoin (1 - s) (sub_nonneg.mpr hs1) (by linarith)
  else PMF.pure false

def continuation : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

def profileP (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (root owner s hs0 hs1)
    continuation

def profileQ (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (root blocker s hs0 hs1)
    continuation

/-- The common successor in the splice comparison: player two quits surely. -/
def collisionContinuation : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {successor})

def splicedP (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (root owner s hs0 hs1)
    collisionContinuation

def splicedQ (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (root blocker s hs0 hs1)
    collisionContinuation

@[simp] theorem quittingQuitters_vec3 (a b c : Bool) :
    quittingQuitters ![a, b, c] =
      (if a then {owner} else ∅) ∪
        (if b then {blocker} else ∅) ∪
          (if c then {successor} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;>
    simp [quittingQuitters, owner, blocker, successor]

@[simp] theorem root_marked_true
    (marked : Player) (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    ((root marked s hs0 hs1 marked) true).toReal = 1 - s := by
  simp [root]

@[simp] theorem root_marked_false
    (marked : Player) (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    ((root marked s hs0 hs1 marked) false).toReal = s := by
  simp [root]

@[simp] theorem root_other_true
    (marked who : Player) (hne : who ≠ marked)
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    ((root marked s hs0 hs1 who) true).toReal = 0 := by
  simp [root, hne]

@[simp] theorem root_other_false
    (marked who : Player) (hne : who ≠ marked)
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    ((root marked s hs0 hs1 who) false).toReal = 1 := by
  simp [root, hne]

@[simp] theorem continuation_payoff (who : Player) :
    quittingTerminalPayoff reward continuation who = 0 := by
  unfold continuation
  rw [quittingTerminalPayoff_pureSetRoot]
  simp

@[simp] theorem continuation_envelope (who : Player) :
    quittingContinuationBestResponseValue reward continuation who =
      if who = owner then 1 else 0 := by
  unfold continuation
  rw [quittingContinuationBestResponseValue_pureSetRoot_eq reward ∅ who]
  fin_cases who <;>
    norm_num [quittingSetReward, reward, owner, blocker, successor, Fin.ext_iff]

@[simp] theorem collisionContinuation_payoff (who : Player) :
    quittingTerminalPayoff reward collisionContinuation who = 0 := by
  have h2 : ({successor} : Finset Player) ≠ {owner, successor} := by decide
  unfold collisionContinuation
  rw [quittingTerminalPayoff_pureSetRoot]
  fin_cases who <;>
    norm_num [quittingSetReward, reward, owner, blocker, successor,
      Fin.ext_iff, h2]

@[simp] theorem collisionContinuation_envelope (who : Player) :
    quittingContinuationBestResponseValue reward collisionContinuation who =
      if who = owner then 2 else 0 := by
  have h02_0 : ({owner, successor} : Finset Player) ≠ {owner} := by decide
  have h02_1 : ({owner, successor} : Finset Player) ≠ {blocker} := by decide
  have h2_02 : ({successor} : Finset Player) ≠ {owner, successor} := by decide
  unfold collisionContinuation
  rw [quittingContinuationBestResponseValue_pureSetRoot_eq
    reward {successor} who]
  fin_cases who <;>
    norm_num [quittingSetReward, reward, owner, blocker, successor,
      Fin.ext_iff, h02_0, h02_1, h2_02]

theorem rootP_quitPayoff_owner
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (root owner s hs0 hs1) owner = 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, blocker, successor,
    expect_eq_sum]

theorem rootP_continuePayoff_owner
    (s c : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingRootContinuePayoff reward (Function.update (0 : Payoff Player)
      owner c) (root owner s hs0 hs1) owner = c := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, blocker, successor,
    expect_eq_sum]

theorem rootQ_quitPayoff_owner
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (root blocker s hs0 hs1) owner = s := by
  have h10_1 : ({blocker, owner} : Finset Player) ≠ {blocker} := by decide
  have h10_02 : ({blocker, owner} : Finset Player) ≠
      {owner, successor} := by decide
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, blocker, successor,
    expect_eq_sum, h10_1, h10_02]

theorem rootQ_continuePayoff_owner
    (s c : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingRootContinuePayoff reward (Function.update (0 : Payoff Player)
      owner c) (root blocker s hs0 hs1) owner = 1 - s + s * c := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, blocker, successor,
    expect_eq_sum]

theorem rootP_successorPayoff_owner
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingRootSuccessorPayoff reward (0 : Payoff Player)
      (root owner s hs0 hs1) owner = 1 - s := by
  have hc := rootP_continuePayoff_owner s 0 hs0 hs1
  simp at hc
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    rootP_quitPayoff_owner, hc]
  simp [root]

theorem rootQ_successorPayoff_owner
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingRootSuccessorPayoff reward (0 : Payoff Player)
      (root blocker s hs0 hs1) owner = 1 - s := by
  have hc := rootQ_continuePayoff_owner s 0 hs0 hs1
  simp at hc
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    rootQ_quitPayoff_owner, hc]
  simp [root, owner, blocker]

theorem root_successorPayoff_other
    (marked : Player) (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1)
    (who : Player) (hwho : who ≠ owner) :
    quittingRootSuccessorPayoff reward (0 : Payoff Player)
      (root marked s hs0 hs1) who = 0 := by
  unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [root, quittingRootPayoff, reward, owner, expect_eq_sum, hwho]

theorem root_quitPayoff_other
    (marked : Player) (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1)
    (who : Player) (hwho : who ≠ owner) (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail (root marked s hs0 hs1) who = 0 := by
  fin_cases who
  · exact absurd rfl hwho
  · unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin3]
    simp [root, quittingRootPayoff, reward, owner, expect_eq_sum]
  · unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin3]
    simp [root, quittingRootPayoff, reward, owner, expect_eq_sum]

theorem root_continuePayoff_other
    (marked : Player) (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1)
    (who : Player) (hwho : who ≠ owner) :
    quittingRootContinuePayoff reward (0 : Payoff Player)
      (root marked s hs0 hs1) who = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  simp [quittingRootPayoff, reward, owner, expect_eq_sum, hwho]

def commonPair (s : Real) : QuittingTerminalSemanticPair Player :=
  (fun who => if who = owner then 1 - s else 0,
    fun who => if who = owner then 1 else 0)

theorem continuation_semanticPair :
    quittingTerminalSemanticPair reward continuation =
      ((0 : Payoff Player), fun who => if who = owner then 1 else 0) := by
  apply Prod.ext <;> funext who
  · exact continuation_payoff who
  · exact continuation_envelope who

theorem profileP_semanticPair
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingTerminalSemanticPair reward (profileP s hs0 hs1) =
      commonPair s := by
  rw [profileP, quittingTerminalSemanticPair_rootThenContinuation]
  rw [continuation_semanticPair]
  unfold quittingTerminalSemanticPrefix commonPair
  dsimp only
  apply Prod.ext
  · funext who
    fin_cases who
    · exact rootP_successorPayoff_owner s hs0 hs1
    · exact root_successorPayoff_other owner s hs0 hs1 1 (by decide)
    · exact root_successorPayoff_other owner s hs0 hs1 2 (by decide)
  · funext who
    fin_cases who
    · change max
        (quittingRootQuitPayoff reward (0 : Payoff Player)
          (root owner s hs0 hs1) owner)
        (quittingRootContinuePayoff reward
          (Function.update (0 : Payoff Player) owner 1)
          (root owner s hs0 hs1) owner) = 1
      rw [rootP_quitPayoff_owner, rootP_continuePayoff_owner]
      norm_num
    · change max
        (quittingRootQuitPayoff reward (0 : Payoff Player)
          (root owner s hs0 hs1) 1)
        (quittingRootContinuePayoff reward (0 : Payoff Player)
          (root owner s hs0 hs1) 1) = 0
      rw [root_quitPayoff_other owner s hs0 hs1 1 (by decide),
        root_continuePayoff_other owner s hs0 hs1 1 (by decide)]
      norm_num
    · change max
        (quittingRootQuitPayoff reward (0 : Payoff Player)
          (root owner s hs0 hs1) 2)
        (quittingRootContinuePayoff reward (0 : Payoff Player)
          (root owner s hs0 hs1) 2) = 0
      rw [root_quitPayoff_other owner s hs0 hs1 2 (by decide),
        root_continuePayoff_other owner s hs0 hs1 2 (by decide)]
      norm_num

theorem profileQ_semanticPair
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingTerminalSemanticPair reward (profileQ s hs0 hs1) =
      commonPair s := by
  rw [profileQ, quittingTerminalSemanticPair_rootThenContinuation]
  rw [continuation_semanticPair]
  unfold quittingTerminalSemanticPrefix commonPair
  dsimp only
  apply Prod.ext
  · funext who
    fin_cases who
    · exact rootQ_successorPayoff_owner s hs0 hs1
    · exact root_successorPayoff_other blocker s hs0 hs1 1 (by decide)
    · exact root_successorPayoff_other blocker s hs0 hs1 2 (by decide)
  · funext who
    fin_cases who
    · change max
        (quittingRootQuitPayoff reward (0 : Payoff Player)
          (root blocker s hs0 hs1) owner)
        (quittingRootContinuePayoff reward
          (Function.update (0 : Payoff Player) owner 1)
          (root blocker s hs0 hs1) owner) = 1
      rw [rootQ_quitPayoff_owner, rootQ_continuePayoff_owner]
      simpa using max_eq_right hs1
    · change max
        (quittingRootQuitPayoff reward (0 : Payoff Player)
          (root blocker s hs0 hs1) 1)
        (quittingRootContinuePayoff reward (0 : Payoff Player)
          (root blocker s hs0 hs1) 1) = 0
      rw [root_quitPayoff_other blocker s hs0 hs1 1 (by decide),
        root_continuePayoff_other blocker s hs0 hs1 1 (by decide)]
      norm_num
    · change max
        (quittingRootQuitPayoff reward (0 : Payoff Player)
          (root blocker s hs0 hs1) 2)
        (quittingRootContinuePayoff reward (0 : Payoff Player)
          (root blocker s hs0 hs1) 2) = 0
      rw [root_quitPayoff_other blocker s hs0 hs1 2 (by decide),
        root_continuePayoff_other blocker s hs0 hs1 2 (by decide)]
      norm_num

theorem semanticPair_eq
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingTerminalSemanticPair reward (profileP s hs0 hs1) =
      quittingTerminalSemanticPair reward (profileQ s hs0 hs1) := by
  rw [profileP_semanticPair, profileQ_semanticPair]

theorem jointSurvival_P
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingStationaryContinueMass (root owner s hs0 hs1) = s := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  simp [root, owner]

theorem jointSurvival_Q
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingStationaryContinueMass (root blocker s hs0 hs1) = s := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  simp [root, blocker]

theorem jointSurvival_eq
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingStationaryContinueMass (root owner s hs0 hs1) =
      quittingStationaryContinueMass (root blocker s hs0 hs1) := by
  rw [jointSurvival_P, jointSurvival_Q]

theorem deletedSurvival_P
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingRootOpponentContinueMass (root owner s hs0 hs1) owner = 1 := by
  unfold quittingRootOpponentContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  simp [root, owner]

theorem deletedSurvival_Q
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingRootOpponentContinueMass (root blocker s hs0 hs1) owner = s := by
  unfold quittingRootOpponentContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  simp [root, owner, blocker]

theorem deletedSurvival_ne
    (s : Real) (hs0 : 0 <= s) (hs1 : s < 1) :
    quittingRootOpponentContinueMass
        (root owner s hs0 hs1.le) owner ≠
      quittingRootOpponentContinueMass
        (root blocker s hs0 hs1.le) owner := by
  rw [deletedSurvival_P, deletedSurvival_Q]
  exact ne_of_gt hs1

theorem collisionContinuation_semanticPair :
    quittingTerminalSemanticPair reward collisionContinuation =
      ((0 : Payoff Player), fun who => if who = owner then 2 else 0) := by
  apply Prod.ext <;> funext who
  · exact collisionContinuation_payoff who
  · exact collisionContinuation_envelope who

theorem splicedP_envelope_owner
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    (quittingTerminalSemanticPair reward (splicedP s hs0 hs1)).2 owner = 2 := by
  rw [splicedP, quittingTerminalSemanticPair_rootThenContinuation,
    collisionContinuation_semanticPair]
  change max
      (quittingRootQuitPayoff reward (0 : Payoff Player)
        (root owner s hs0 hs1) owner)
      (quittingRootContinuePayoff reward
        (Function.update (0 : Payoff Player) owner 2)
        (root owner s hs0 hs1) owner) = 2
  rw [rootP_quitPayoff_owner, rootP_continuePayoff_owner]
  norm_num

theorem splicedQ_envelope_owner
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    (quittingTerminalSemanticPair reward (splicedQ s hs0 hs1)).2 owner =
      1 + s := by
  rw [splicedQ, quittingTerminalSemanticPair_rootThenContinuation,
    collisionContinuation_semanticPair]
  change max
      (quittingRootQuitPayoff reward (0 : Payoff Player)
        (root blocker s hs0 hs1) owner)
      (quittingRootContinuePayoff reward
        (Function.update (0 : Payoff Player) owner 2)
        (root blocker s hs0 hs1) owner) = 1 + s
  rw [rootQ_quitPayoff_owner, rootQ_continuePayoff_owner]
  have hle : s <= 1 - s + s * 2 := by linarith
  rw [max_eq_right hle]
  ring

theorem spliced_envelope_ne
    (s : Real) (hs0 : 0 < s) (hs1 : s < 1) :
    (quittingTerminalSemanticPair reward
        (splicedP s hs0.le hs1.le)).2 owner ≠
      (quittingTerminalSemanticPair reward
        (splicedQ s hs0.le hs1.le)).2 owner := by
  rw [splicedP_envelope_owner, splicedQ_envelope_owner]
  linarith

theorem pureTime_one_eq_rootAndContinuation :
    quittingPureTimeBehaviorStrategy reward owner (some 1) =
      quittingRootAndContinuationDeviation reward (PMF.pure false)
        (quittingPureTimeBehaviorStrategy reward owner (some 0)) := by
  funext time history
  cases time with
  | zero => rfl
  | succ time =>
      cases time <;>
        simp [quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
          quittingRootAndContinuationDeviation]

theorem pureTime_zero_continuation_payoff :
    quittingTerminalPayoff reward
        (Function.update continuation owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner = 1 := by
  unfold continuation
  simpa [quittingSetReward, reward, owner, blocker, successor] using
    (quittingTerminalPayoff_update_pureSetRoot_quitNow
      reward (∅ : Finset Player) owner)

theorem commonPureTimeWitness_P
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingTerminalPayoff reward
        (Function.update (profileP s hs0 hs1) owner
          (quittingPureTimeBehaviorStrategy reward owner (some 1))) owner =
      (quittingTerminalSemanticPair reward (profileP s hs0 hs1)).2 owner := by
  rw [profileP_semanticPair]
  change quittingTerminalPayoff reward
      (Function.update (profileP s hs0 hs1) owner
        (quittingPureTimeBehaviorStrategy reward owner (some 1))) owner = 1
  rw [pureTime_one_eq_rootAndContinuation]
  unfold profileP
  rw [quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
  simp only [continuation_payoff, pureTime_zero_continuation_payoff]
  change quittingRootContinuePayoff reward
      (Function.update (0 : Payoff Player) owner 1)
      (root owner s hs0 hs1) owner = 1
  exact rootP_continuePayoff_owner s 1 hs0 hs1

theorem commonPureTimeWitness_Q
    (s : Real) (hs0 : 0 <= s) (hs1 : s <= 1) :
    quittingTerminalPayoff reward
        (Function.update (profileQ s hs0 hs1) owner
          (quittingPureTimeBehaviorStrategy reward owner (some 1))) owner =
      (quittingTerminalSemanticPair reward (profileQ s hs0 hs1)).2 owner := by
  rw [profileQ_semanticPair]
  change quittingTerminalPayoff reward
      (Function.update (profileQ s hs0 hs1) owner
        (quittingPureTimeBehaviorStrategy reward owner (some 1))) owner = 1
  rw [pureTime_one_eq_rootAndContinuation]
  unfold profileQ
  rw [quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
  simp only [continuation_payoff, pureTime_zero_continuation_payoff]
  change quittingRootContinuePayoff reward
      (Function.update (0 : Payoff Player) owner 1)
      (root blocker s hs0 hs1) owner = 1
  rw [rootQ_continuePayoff_owner]
  ring

/-- Exact bundled regression: the same pair, joint survival, and pure witness
coexist with unequal deleted clocks and unequal values after the same splice. -/
theorem exists_terminalSemantic_commonWitness_noncompositionality :
    ∃ s : Real, ∃ hs0 : 0 < s, ∃ hs1 : s < 1,
      quittingTerminalSemanticPair reward (profileP s hs0.le hs1.le) =
          quittingTerminalSemanticPair reward (profileQ s hs0.le hs1.le) ∧
        quittingStationaryContinueMass (root owner s hs0.le hs1.le) =
          quittingStationaryContinueMass (root blocker s hs0.le hs1.le) ∧
        quittingTerminalPayoff reward
            (Function.update (profileP s hs0.le hs1.le) owner
              (quittingPureTimeBehaviorStrategy reward owner (some 1))) owner =
          (quittingTerminalSemanticPair reward
            (profileP s hs0.le hs1.le)).2 owner ∧
        quittingTerminalPayoff reward
            (Function.update (profileQ s hs0.le hs1.le) owner
              (quittingPureTimeBehaviorStrategy reward owner (some 1))) owner =
          (quittingTerminalSemanticPair reward
            (profileQ s hs0.le hs1.le)).2 owner ∧
        quittingRootOpponentContinueMass
            (root owner s hs0.le hs1.le) owner ≠
          quittingRootOpponentContinueMass
            (root blocker s hs0.le hs1.le) owner ∧
        (quittingTerminalSemanticPair reward
            (splicedP s hs0.le hs1.le)).2 owner ≠
          (quittingTerminalSemanticPair reward
            (splicedQ s hs0.le hs1.le)).2 owner := by
  have hs0 : (0 : Real) < 1 / 2 := by norm_num
  have hs1 : (1 / 2 : Real) < 1 := by norm_num
  refine ⟨1 / 2, hs0, hs1, ?_⟩
  exact ⟨semanticPair_eq (1 / 2) hs0.le hs1.le,
    jointSurvival_eq (1 / 2) hs0.le hs1.le,
    commonPureTimeWitness_P (1 / 2) hs0.le hs1.le,
    commonPureTimeWitness_Q (1 / 2) hs0.le hs1.le,
    deletedSurvival_ne (1 / 2) hs0.le hs1,
    spliced_envelope_ne (1 / 2) hs0 hs1⟩

end QuittingCommonWitnessNoncompositionality

end GameTheory
