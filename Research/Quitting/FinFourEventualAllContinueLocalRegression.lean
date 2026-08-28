/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.MaximalCapSemanticPrefixOrbit
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapFullSupportLift
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonResidualHard
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# The exact rational local regression for an all-Continue ray stall

This file implements the rational table displayed in
`FIN4_EVENTUAL_ALLCONTINUE_STALL_NORMAL_FORM_AND_LOCAL_REGRESSION.md`.
It is intentionally separate from the other zero-minimum ray regressions:
the reward table here is the packet's table, not a substitute with similar
local fields.

The pure pair `{0,1}` has prescribed payoff `(1,4,1,2)`, full behavioral cap
`(3,4,2,2)`, and debt `(2,0,1,0)`.  Player `2` has a literal unit-gain endpoint
and player `1` has zero debt.  All Continue is the unique exact product root
at that cap, so the autonomous maximal-prefix semantic ray is fixed at once.

The same table has zero own-singleton rewards.  Hence the all-Never behavioral
profile is an exact Nash profile, the terminal-semantic global minimum is zero,
and zero is a uniform-equilibrium payoff.  This is a boundary regression and
cannot be attached to a positive-minimum producer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct Set
open QuittingLCPClassification QuittingSureSetOwnerRepair

namespace FinFourEventualAllContinueLocalRegression

abbrev Player := Fin 4

/-! ## The advertised reward table -/

/-- The paired normalized singleton matrix from equation (4). -/
def singletonMatrix : Player → Player → ℝ :=
  FourPlayerPairedSingleton.pairedSingletonMatrix

/-- Passive value `f_i(T)`: singleton entries come from the matrix; the only
nonsingleton exceptions are `f₂({0,1})=1` and `f₃({0,1})=2`. -/
def passiveValue (who : Player) (terminal : Finset Player) : ℝ :=
  if terminal = {0} then singletonMatrix who 0
  else if terminal = {1} then singletonMatrix who 1
  else if terminal = {2} then singletonMatrix who 2
  else if terminal = {3} then singletonMatrix who 3
  else if who = 2 ∧ terminal = {0, 1} then 1
  else if who = 3 ∧ terminal = {0, 1} then 2
  else 0

/-- Membership increment `g_i(T)` from equation (6). -/
def membershipGain (who : Player) (terminal : Finset Player) : ℝ :=
  ![(if 3 ∈ terminal then 1 else 0) - 2 * (if 1 ∈ terminal then 1 else 0),
    (if 0 ∈ terminal then 1 else 0) - 2 * (if 3 ∈ terminal then 1 else 0),
    (if 0 ∈ terminal then 1 else 0) - 2 * (if 3 ∈ terminal then 1 else 0),
    (if 1 ∈ terminal then 1 else 0) - 2 * (if 0 ∈ terminal then 1 else 0)] who

/-- Complete reward table from equations (4)--(7). -/
def reward
    (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who ↦
    if who ∈ terminal.val then
      passiveValue who (terminal.val.erase who) +
        membershipGain who (terminal.val.erase who)
    else passiveValue who terminal.val

/-- Every own-singleton payoff is zero. -/
theorem reward_ownSingleton_eq_zero (who : Player) :
    reward (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;>
    norm_num +decide [reward, passiveValue, membershipGain, singletonMatrix,
      FourPlayerPairedSingleton.pairedSingletonMatrix,
      quittingSingletonTerminal]

/-- The complete singleton payoff vectors are exactly the paired matrix. -/
theorem reward_singleton_eq_matrix (owner : Player) :
    reward (quittingSingletonTerminal owner) = fun who ↦
      singletonMatrix who owner := by
  funext who
  fin_cases owner <;> fin_cases who <;>
    norm_num +decide [reward, passiveValue, membershipGain, singletonMatrix,
      FourPlayerPairedSingleton.pairedSingletonMatrix,
      quittingSingletonTerminal, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- Normalization does not alter the displayed zero-diagonal matrix. -/
theorem normalizedSoloMatrix_eq :
    normalizedSoloMatrix reward = singletonMatrix := by
  funext who owner
  rw [normalizedSoloMatrix,
    normalized_singletonMatrix_eq_quittingSingletonMatrix,
    quittingSingletonMatrix]
  change reward (quittingSingletonTerminal owner) who -
      reward (quittingSingletonTerminal who) who = singletonMatrix who owner
  rw [congrFun (reward_singleton_eq_matrix owner) who,
    reward_ownSingleton_eq_zero]
  ring

/-- Every player belongs to the normal core. -/
theorem normalCore_eq_univ :
    normalCore (normalizedSoloMatrix reward) = Finset.univ := by
  rw [normalizedSoloMatrix_eq]
  exact FourPlayerPairedSingleton.pairedSingletonMatrix_normalCore_eq_univ

/-- The exact table lies in the same residual-hard matrix class as every
completion with the paired normalized singleton matrix. -/
theorem residualHardClass : ResidualHardClass reward := by
  have hmatrix : normalizedSoloMatrix reward = normalizedSoloMatrix
      FourPlayerPairedSingleton.stationaryCompletionReward := by
    rw [normalizedSoloMatrix_eq,
      FourPlayerPairedSingleton.normalizedSoloMatrix_stationaryCompletion]
    rfl
  have href := FourPlayerPairedSingleton.stationaryCompletion_residualHardClass
  refine {
    normal_nonempty := ?_
    no_homogeneous := ?_
    normal_standardQ := ?_
    not_full_projectiveQBar := ?_
  }
  · rw [hmatrix]
    exact href.normal_nonempty
  · rw [normalizedNormalPlayerMatrix, hmatrix]
    exact href.no_homogeneous
  · rw [normalizedNormalPlayerMatrix, hmatrix]
    exact href.normal_standardQ
  · rw [hmatrix]
    exact href.not_full_projectiveQBar

/-! ## Punishment normality and the uniform singleton packet -/

/-- Every player is punishment-normal. -/
theorem normal (who : Player) : IsQuittingNormalPlayer reward who := by
  unfold IsQuittingNormalPlayer quittingSoloSelfPayoff
  have hupper := quittingPunishmentValue_le_max_solo reward who
  have hsolo : quittingSetReward reward ({who} : Finset Player) who = 0 := by
    change reward (quittingSingletonTerminal who) who = 0
    exact reward_ownSingleton_eq_zero who
  rw [hsolo, max_eq_right (le_refl 0)] at hupper
  change quittingPunishmentValue reward who ≤
    reward (quittingSingletonTerminal who) who
  rwa [reward_ownSingleton_eq_zero]

/-- Uniform full-support singleton mass. -/
def singletonMass (_owner : Player) : ℝ := 1 / 4

theorem singletonMass_pos (owner : Player) : 0 < singletonMass owner := by
  norm_num [singletonMass]

theorem singletonMass_sum : ∑ owner, singletonMass owner = 1 := by
  norm_num [singletonMass, Fin.sum_univ_four]

/-- Every row of the paired singleton matrix averages to `1/4`. -/
theorem uniformSingletonMixture_eq (who : Player) :
    quittingSingletonMixture reward singletonMass who = 1 / 4 := by
  fin_cases who <;>
    norm_num [quittingSingletonMixture, singletonMass,
      reward_singleton_eq_matrix, singletonMatrix,
      FourPlayerPairedSingleton.pairedSingletonMatrix, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

/-- Literal full-support normalized singleton packet of mass `1/4`. -/
def singletonPacket : QuittingNormalizedSingletonSourcePacket reward :=
  normalFullSupportSingletonPacket reward singletonMass
    (fun owner ↦ (singletonMass_pos owner).le) singletonMass_sum normal (by
      intro who
      rw [reward_ownSingleton_eq_zero, uniformSingletonMixture_eq]
      norm_num)

theorem singletonPacket_support_eq_univ :
    singletonPacket.support = Finset.univ := by
  ext owner
  simp [QuittingNormalizedSingletonSourcePacket.support, singletonPacket,
    normalFullSupportSingletonPacket, singletonMass_pos]

/-! ## The literal pair, cap, debt, and paid endpoint -/

def pairTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{0, 1}, by simp⟩

def pairPayoff : Payoff Player := ![1, 4, 1, 2]

def pairCap : Payoff Player := ![3, 4, 2, 2]

def pairDebt : Payoff Player := ![2, 0, 1, 0]

def neverProfile : (quittingGame reward).BehaviorProfile :=
  quittingAlwaysContinueProfile reward

/-- One actual finite-clock profile: the pure pair quits at date zero and the
counterfactual post-date continuation is all Never. -/
def pairProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingPureSetRoot pairTerminal.val) neverProfile

/-- The pair's full prescribed-payoff/unrestricted-behavioral-cap semantic
pair is exactly `(U,B)` from the packet. -/
theorem pair_semantic_eq :
    quittingTerminalSemanticPair reward pairProfile = (pairPayoff, pairCap) := by
  rw [pairProfile,
    quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      reward pairTerminal.val (by decide) neverProfile]
  apply Prod.ext
  · funext who
    fin_cases who <;>
      norm_num +decide [pairTerminal, pairPayoff, quittingSetReward, reward,
        passiveValue, membershipGain, singletonMatrix,
        FourPlayerPairedSingleton.pairedSingletonMatrix]
  · funext who
    fin_cases who <;>
      norm_num +decide [pairTerminal, pairCap, quittingSetReward, reward,
        passiveValue, membershipGain, singletonMatrix,
        FourPlayerPairedSingleton.pairedSingletonMatrix]

theorem pair_terminalPayoff_eq :
    quittingTerminalPayoff reward pairProfile = pairPayoff := by
  change (quittingTerminalSemanticPair reward pairProfile).1 = pairPayoff
  exact congrArg Prod.fst pair_semantic_eq

/-- This is the full unrestricted behavioral cap, not a stationary cap. -/
theorem pair_bestResponse_eq :
    quittingContinuationBestResponseValue reward pairProfile = pairCap := by
  change (quittingTerminalSemanticPair reward pairProfile).2 = pairCap
  exact congrArg Prod.snd pair_semantic_eq

theorem pair_debt_eq :
    (fun who ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward pairProfile) who) = pairDebt := by
  funext who
  rw [pair_semantic_eq]
  fin_cases who <;>
    norm_num [quittingTerminalSemanticDebt, pairPayoff, pairCap, pairDebt]

/-- Player `1` is the zero-debt forced owner at the pair. -/
theorem owner_one_debt_eq_zero :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward pairProfile) 1 = 0 := by
  rw [congrFun pair_debt_eq 1]
  rfl

/-- Player `2` is the distinct outside payer with exact unit debt. -/
theorem payer_two_debt_eq_one :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward pairProfile) 2 = 1 := by
  rw [congrFun pair_debt_eq 2]
  rfl

def payerEndpointProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingPureSetRoot ({0, 1, 2} : Finset Player)) neverProfile

/-- The pair and payer endpoint differ only in player `2`'s full strategy. -/
theorem payerEndpoint_opponent_eq (other : Player) (hother : other ≠ 2) :
    payerEndpointProfile other = pairProfile other := by
  funext time history
  cases time with
  | zero =>
      simp [payerEndpointProfile, pairProfile, quittingRootThenContinuationProfile,
        quittingPureSetRoot, quittingSetAction, pairTerminal, hother]
  | succ time =>
      simp [payerEndpointProfile, pairProfile, quittingRootThenContinuationProfile]

theorem update_pairProfile_payer_eq_endpoint :
    Function.update pairProfile 2 (payerEndpointProfile 2) =
      payerEndpointProfile := by
  apply funext
  intro who
  by_cases hwho : who = 2
  · subst who
    simp
  · simp [hwho, (payerEndpoint_opponent_eq who hwho).symm]

theorem payerEndpoint_payoff_eq_two :
    quittingTerminalPayoff reward payerEndpointProfile 2 = 2 := by
  rw [payerEndpointProfile,
    quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
      ({0, 1, 2} : Finset Player) (by simp) neverProfile 2]
  norm_num +decide [quittingSetReward, reward, passiveValue, membershipGain,
    singletonMatrix, FourPlayerPairedSingleton.pairedSingletonMatrix,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem payerEndpoint_gain_eq_one :
    quittingTerminalPayoff reward payerEndpointProfile 2 -
      quittingTerminalPayoff reward pairProfile 2 = 1 := by
  rw [payerEndpoint_payoff_eq_two, congrFun pair_terminalPayoff_eq 2]
  norm_num [pairPayoff, Matrix.cons_val_two]

theorem payerEndpoint_bestResponse_eq_two :
    quittingContinuationBestResponseValue reward payerEndpointProfile 2 = 2 := by
  rw [← update_pairProfile_payer_eq_endpoint,
    quittingContinuationBestResponseValue_update_self,
    congrFun pair_bestResponse_eq 2]
  rfl

theorem payerEndpoint_debt_eq_zero :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward payerEndpointProfile) 2 = 0 := by
  change quittingContinuationBestResponseValue reward payerEndpointProfile 2 -
      quittingTerminalPayoff reward payerEndpointProfile 2 = 0
  rw [payerEndpoint_bestResponse_eq_two, payerEndpoint_payoff_eq_two]
  norm_num

/-! ## Exact endpoint geometry and unique all-Continue root -/

theorem endpointDifference_zero (root : Player → PMF Bool) :
    quittingRootEndpointDifference reward pairCap root 0 =
      (root 3 true).toReal - 2 * (root 1 true).toReal -
        3 * (root 1 false).toReal * (root 2 false).toReal *
          (root 3 false).toReal := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  rw [show ((Finset.univ.erase (0 : Player)).powerset) =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
  have herase : Finset.univ.erase (0 : Player) = {1, 2, 3} := by decide
  have hdiff12 : ({2, 3} : Finset Player) \ {1, 2} = {3} := by decide
  have hdiff13 : ({2, 3} : Finset Player) \ {1, 3} = {2} := by decide
  have hdiff1 : ({1, 2, 3} : Finset Player) \ {1} = {2, 3} := by decide
  have hdiff3 : ({1, 2, 3} : Finset Player) \ {3} = {1, 2} := by decide
  norm_num +decide [quittingOpponentCoalitionMass, Finset.prod_insert,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    reward, passiveValue, membershipGain, singletonMatrix,
    FourPlayerPairedSingleton.pairedSingletonMatrix, pairCap,
    pmfBool_false_toReal, herase, hdiff12, hdiff13, hdiff1, hdiff3,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem endpointDifference_one (root : Player → PMF Bool) :
    quittingRootEndpointDifference reward pairCap root 1 =
      (root 0 true).toReal - 2 * (root 3 true).toReal -
        4 * (root 0 false).toReal * (root 2 false).toReal *
          (root 3 false).toReal := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  rw [show ((Finset.univ.erase (1 : Player)).powerset) =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
  have herase : Finset.univ.erase (1 : Player) = {0, 2, 3} := by decide
  have hdiff02 : ({2, 3} : Finset Player) \ {0, 2} = {3} := by decide
  have hdiff03 : ({2, 3} : Finset Player) \ {0, 3} = {2} := by decide
  have hdiff0 : ({0, 2, 3} : Finset Player) \ {0} = {2, 3} := by decide
  have hdiff3 : ({0, 2, 3} : Finset Player) \ {3} = {0, 2} := by decide
  norm_num +decide [quittingOpponentCoalitionMass, Finset.prod_insert,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    reward, passiveValue, membershipGain, singletonMatrix,
    FourPlayerPairedSingleton.pairedSingletonMatrix, pairCap,
    pmfBool_false_toReal, herase, hdiff02, hdiff03, hdiff0, hdiff3,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem endpointDifference_two (root : Player → PMF Bool) :
    quittingRootEndpointDifference reward pairCap root 2 =
      (root 0 true).toReal - 2 * (root 3 true).toReal -
        2 * (root 0 false).toReal * (root 1 false).toReal *
          (root 3 false).toReal := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  rw [show ((Finset.univ.erase (2 : Player)).powerset) =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
  have herase : Finset.univ.erase (2 : Player) = {0, 1, 3} := by decide
  have hdiff01 : ({1, 3} : Finset Player) \ {0, 1} = {3} := by decide
  have hdiff03 : ({1, 3} : Finset Player) \ {0, 3} = {1} := by decide
  have hdiff0 : ({0, 1, 3} : Finset Player) \ {0} = {1, 3} := by decide
  have hdiff3 : ({0, 1, 3} : Finset Player) \ {3} = {0, 1} := by decide
  norm_num +decide [quittingOpponentCoalitionMass, Finset.prod_insert,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    reward, passiveValue, membershipGain, singletonMatrix,
    FourPlayerPairedSingleton.pairedSingletonMatrix, pairCap,
    pmfBool_false_toReal, herase, hdiff01, hdiff03, hdiff0, hdiff3,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem endpointDifference_three (root : Player → PMF Bool) :
    quittingRootEndpointDifference reward pairCap root 3 =
      (root 1 true).toReal - 2 * (root 0 true).toReal -
        2 * (root 0 false).toReal * (root 1 false).toReal *
          (root 2 false).toReal := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  rw [show ((Finset.univ.erase (3 : Player)).powerset) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  have herase : Finset.univ.erase (3 : Player) = {0, 1, 2} := by decide
  have hdiff01 : ({1, 2} : Finset Player) \ {0, 1} = {2} := by decide
  have hdiff02 : ({1, 2} : Finset Player) \ {0, 2} = {1} := by decide
  have hdiff0 : ({0, 1, 2} : Finset Player) \ {0} = {1, 2} := by decide
  have hdiff1 : ({0, 1, 2} : Finset Player) \ {1} = {0, 2} := by decide
  norm_num +decide [quittingOpponentCoalitionMass, Finset.prod_insert,
    quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    reward, passiveValue, membershipGain, singletonMatrix,
    FourPlayerPairedSingleton.pairedSingletonMatrix, pairCap,
    pmfBool_false_toReal, herase, hdiff01, hdiff02, hdiff0, hdiff1,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem endpointDifference_nonneg_of_quitRate_ne_zero
    (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward pairCap 0 root)
    (who : Player) (hquit : (root who true).toReal ≠ 0) :
    0 ≤ quittingRootEndpointDifference reward pairCap root who := by
  have hendpoint :=
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward pairCap root).2 hnash)
  rcases sureContinue_or_nonnegative_endpointDifference_of_isZeroNash
      reward pairCap root who hendpoint with hzero | hnonneg
  · exact (hquit hzero).elim
  · exact hnonneg

private theorem endpointDifference_nonpos_of_quitRate_eq_zero
    (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward pairCap 0 root)
    (who : Player) (hquit : (root who true).toReal = 0) :
    quittingRootEndpointDifference reward pairCap root who ≤ 0 := by
  have hendpoint :=
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward pairCap root).2 hnash)
  rcases sureQuit_or_nonpositive_endpointDifference_of_isZeroNash
      reward pairCap root who hendpoint with hone | hnonpos
  · rw [hquit] at hone
    norm_num at hone
  · exact hnonpos

/-- The packet's inequalities (8) force every exact product root at `B` to be
literally all Continue. -/
theorem exactRoot_eq_allContinue
    (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward pairCap 0 root) :
    root = (quittingAllContinueRoot : Player → PMF Bool) := by
  let x0 := (root 0 true).toReal
  let x1 := (root 1 true).toReal
  let x2 := (root 2 true).toReal
  let x3 := (root 3 true).toReal
  have hx0nonneg : 0 ≤ x0 := ENNReal.toReal_nonneg
  have hx1nonneg : 0 ≤ x1 := ENNReal.toReal_nonneg
  have hx2nonneg : 0 ≤ x2 := ENNReal.toReal_nonneg
  have hx3nonneg : 0 ≤ x3 := ENNReal.toReal_nonneg
  have hx0le : x0 ≤ 1 := by
    dsimp only [x0]
    linarith [pmfBool_false_toReal (root 0),
      show 0 ≤ (root 0 false).toReal from ENNReal.toReal_nonneg]
  have hx1le : x1 ≤ 1 := by
    dsimp only [x1]
    linarith [pmfBool_false_toReal (root 1),
      show 0 ≤ (root 1 false).toReal from ENNReal.toReal_nonneg]
  have hx2le : x2 ≤ 1 := by
    dsimp only [x2]
    linarith [pmfBool_false_toReal (root 2),
      show 0 ≤ (root 2 false).toReal from ENNReal.toReal_nonneg]
  have hx3le : x3 ≤ 1 := by
    dsimp only [x3]
    linarith [pmfBool_false_toReal (root 3),
      show 0 ≤ (root 3 false).toReal from ENNReal.toReal_nonneg]
  have hcontinue0 : (root 0 false).toReal = 1 - x0 := by
    dsimp only [x0]
    linarith [pmfBool_false_toReal (root 0)]
  have hcontinue1 : (root 1 false).toReal = 1 - x1 := by
    dsimp only [x1]
    linarith [pmfBool_false_toReal (root 1)]
  have hcontinue2 : (root 2 false).toReal = 1 - x2 := by
    dsimp only [x2]
    linarith [pmfBool_false_toReal (root 2)]
  have hcontinue3 : (root 3 false).toReal = 1 - x3 := by
    dsimp only [x3]
    linarith [pmfBool_false_toReal (root 3)]
  have hprod0 : 0 ≤ (1 - x1) * (1 - x2) * (1 - x3) := by positivity
  have hprod1 : 0 ≤ (1 - x0) * (1 - x2) * (1 - x3) := by positivity
  have hprod2 : 0 ≤ (1 - x0) * (1 - x1) * (1 - x3) := by positivity
  have hprod3 : 0 ≤ (1 - x0) * (1 - x1) * (1 - x2) := by positivity
  have hx0 : x0 = 0 := by
    by_contra hx0ne
    have hx0pos : 0 < x0 := lt_of_le_of_ne hx0nonneg (Ne.symm hx0ne)
    have hG0 := endpointDifference_nonneg_of_quitRate_ne_zero
      root hnash 0 hx0ne
    rw [endpointDifference_zero, hcontinue1, hcontinue2, hcontinue3] at hG0
    change 0 ≤ x3 - 2 * x1 - 3 * (1 - x1) * (1 - x2) * (1 - x3)
      at hG0
    by_cases hx3 : x3 = 0
    · have hx1 : x1 = 0 := by nlinarith [hG0, hprod0]
      rw [hx3, hx1] at hG0
      ring_nf at hG0
      have hx2 : x2 = 1 := by nlinarith
      have hG1 := endpointDifference_nonpos_of_quitRate_eq_zero
        root hnash 1 (by simpa [x1] using hx1)
      rw [endpointDifference_one, hcontinue0, hcontinue2, hcontinue3] at hG1
      change x0 - 2 * x3 - 4 * (1 - x0) * (1 - x2) * (1 - x3) ≤ 0
        at hG1
      rw [hx3, hx2] at hG1
      ring_nf at hG1
      linarith
    · have hG3 := endpointDifference_nonneg_of_quitRate_ne_zero
        root hnash 3 hx3
      rw [endpointDifference_three, hcontinue0, hcontinue1, hcontinue2] at hG3
      change 0 ≤ x1 - 2 * x0 - 2 * (1 - x0) * (1 - x1) * (1 - x2)
        at hG3
      have hx1ne : x1 ≠ 0 := by
        intro hx1
        nlinarith [hG3, hprod3]
      have hG1 := endpointDifference_nonneg_of_quitRate_ne_zero
        root hnash 1 hx1ne
      rw [endpointDifference_one, hcontinue0, hcontinue2, hcontinue3] at hG1
      change 0 ≤ x0 - 2 * x3 - 4 * (1 - x0) * (1 - x2) * (1 - x3)
        at hG1
      nlinarith [hG0, hG3, hG1, hprod0, hprod1, hprod3]
  have hx1 : x1 = 0 := by
    by_contra hx1ne
    have hx1pos : 0 < x1 := lt_of_le_of_ne hx1nonneg (Ne.symm hx1ne)
    have hG1 := endpointDifference_nonneg_of_quitRate_ne_zero
      root hnash 1 hx1ne
    rw [endpointDifference_one, hcontinue0, hcontinue2, hcontinue3] at hG1
    change 0 ≤ x0 - 2 * x3 - 4 * (1 - x0) * (1 - x2) * (1 - x3)
      at hG1
    have hx3 : x3 = 0 := by nlinarith [hG1, hprod1]
    rw [hx0, hx3] at hG1
    ring_nf at hG1
    have hx2 : x2 = 1 := by nlinarith
    have hG3 := endpointDifference_nonpos_of_quitRate_eq_zero
      root hnash 3 (by simpa [x3] using hx3)
    rw [endpointDifference_three, hcontinue0, hcontinue1, hcontinue2] at hG3
    change x1 - 2 * x0 - 2 * (1 - x0) * (1 - x1) * (1 - x2) ≤ 0
      at hG3
    rw [hx0, hx2] at hG3
    ring_nf at hG3
    linarith
  have hx3 : x3 = 0 := by
    by_contra hx3ne
    have hx3pos : 0 < x3 := lt_of_le_of_ne hx3nonneg (Ne.symm hx3ne)
    have hG3 := endpointDifference_nonneg_of_quitRate_ne_zero
      root hnash 3 hx3ne
    rw [endpointDifference_three, hcontinue0, hcontinue1, hcontinue2] at hG3
    change 0 ≤ x1 - 2 * x0 - 2 * (1 - x0) * (1 - x1) * (1 - x2)
      at hG3
    rw [hx0, hx1] at hG3
    ring_nf at hG3
    have hx2 : x2 = 1 := by nlinarith
    have hG0 := endpointDifference_nonpos_of_quitRate_eq_zero
      root hnash 0 (by simpa [x0] using hx0)
    rw [endpointDifference_zero, hcontinue1, hcontinue2, hcontinue3] at hG0
    change x3 - 2 * x1 - 3 * (1 - x1) * (1 - x2) * (1 - x3) ≤ 0
      at hG0
    rw [hx1, hx2] at hG0
    ring_nf at hG0
    linarith
  have hx2 : x2 = 0 := by
    by_contra hx2ne
    have hx2pos : 0 < x2 := lt_of_le_of_ne hx2nonneg (Ne.symm hx2ne)
    have hG2 := endpointDifference_nonneg_of_quitRate_ne_zero
      root hnash 2 hx2ne
    rw [endpointDifference_two, hcontinue0, hcontinue1, hcontinue3] at hG2
    change 0 ≤ x0 - 2 * x3 - 2 * (1 - x0) * (1 - x1) * (1 - x3)
      at hG2
    rw [hx0, hx1, hx3] at hG2
    norm_num at hG2
  funext who
  fin_cases who
  · exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      (root 0) (by simpa [x0] using hx0)
  · exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      (root 1) (by simpa [x1] using hx1)
  · exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      (root 2) (by simpa [x2] using hx2)
  · exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      (root 3) (by simpa [x3] using hx3)

theorem allContinue_exactRoot :
    IsεQuittingRootNash reward pairCap 0
      (quittingAllContinueRoot : Player → PMF Bool) := by
  apply (isZeroQuittingRootNash_allContinue_iff_singleton_le
    reward pairCap).2
  intro who
  rw [reward_ownSingleton_eq_zero]
  fin_cases who <;> norm_num [pairCap]

/-! ## Immediate canonical-ray stall -/

def pairSemantic : QuittingTerminalSemanticPair Player := (pairPayoff, pairCap)

theorem pairSemantic_eq_profile :
    pairSemantic = quittingTerminalSemanticPair reward pairProfile :=
  pair_semantic_eq.symm

theorem maximalRoot_pairSemantic_eq_allContinue :
    quittingMaximalCapSemanticRoot reward pairSemantic =
      (quittingAllContinueRoot : Player → PMF Bool) := by
  apply exactRoot_eq_allContinue
  exact quittingMaximalCapSemanticRoot_exactNash reward pairSemantic

theorem pairSemantic_prefix_allContinue_eq_self :
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot pairSemantic =
      pairSemantic :=
  quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
    reward pairSemantic (by
      intro who
      rw [reward_ownSingleton_eq_zero]
      fin_cases who <;> norm_num [pairSemantic, pairCap])

theorem maximalPrefixOrbit_pairSemantic_eq (time : ℕ) :
    quittingMaximalCapSemanticPrefixOrbit reward pairSemantic time =
      pairSemantic := by
  induction time with
  | zero => rfl
  | succ time ih =>
      rw [quittingMaximalCapSemanticPrefixOrbit_succ, ih,
        maximalRoot_pairSemantic_eq_allContinue,
        pairSemantic_prefix_allContinue_eq_self]

/-! ## Zero global minimum and literal uniform equilibrium -/

theorem isZeroSolo : IsQuittingZeroSolo reward :=
  fun who ↦ (reward_ownSingleton_eq_zero who).le

theorem neverTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 neverProfile :=
  isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward isZeroSolo

theorem neverTerminalPayoff_eq_zero :
    quittingTerminalPayoff reward neverProfile = (0 : Payoff Player) :=
  funext fun who ↦ quittingTerminalPayoff_quittingAlwaysContinue reward who

def neverPair : QuittingTerminalSemanticPair Player :=
  quittingTerminalSemanticPair reward neverProfile

theorem neverPair_eq_zero :
    neverPair = ((0 : Payoff Player), (0 : Payoff Player)) := by
  apply Prod.ext
  · exact neverTerminalPayoff_eq_zero
  · funext who
    change quittingContinuationBestResponseValue reward neverProfile who = 0
    rw [neverProfile,
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      reward_ownSingleton_eq_zero]
    norm_num

theorem neverPair_mem : neverPair ∈ quittingTerminalSemanticCarrier reward :=
  quittingTerminalSemanticPair_mem_carrier reward neverProfile

theorem neverPair_debtSum_eq_zero :
    quittingTerminalSemanticDebtSum neverPair = 0 := by
  rw [neverPair_eq_zero]
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt]

theorem neverPair_globalMinimum
    (candidate : QuittingTerminalSemanticPair Player)
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticDebtSum neverPair ≤
      quittingTerminalSemanticDebtSum candidate := by
  rw [neverPair_debtSum_eq_zero]
  exact Finset.sum_nonneg fun who _ ↦
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hcandidate who

theorem terminalDebtSumInf_eq_zero :
    quittingTerminalDebtSumInf reward = 0 := by
  rw [quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
    neverPair neverPair_mem neverPair_globalMinimum,
    neverPair_debtSum_eq_zero]

theorem neverUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff Player) :=
  quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward isZeroSolo

/-- The exact local regression cannot coexist with a positive global minimum
for the same reward table. -/
theorem not_hasPositiveMinimumTerminalSemanticDebt :
    ¬ HasPositiveMinimumTerminalSemanticDebt reward := by
  rintro ⟨minimum, hminimumMem, hminimum, hpositive⟩
  have hle := hminimum neverPair neverPair_mem
  rw [neverPair_debtSum_eq_zero] at hle
  linarith

end FinFourEventualAllContinueLocalRegression

end GameTheory
