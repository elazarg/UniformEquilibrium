/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.TerminalDebtSingletonDescent
import UniformEquilibrium.Quitting.Root.ImmediateQuitCapDisplacement
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass
import UniformEquilibrium.Quitting.Root.SingletonGapSemanticDebtDescent
import UniformEquilibrium.Quitting.Terminal.TerminalDebtPrefixDescent

/-!
# Exact-prefix exit from recurring immediate-Quit caps

An immediate-Quit cap at a literal root prefix turns a positive terminal-debt
floor into a lower bound on that root's Quit-versus-Continue endpoint gap.
The endpoint comparison then puts the displayed child payoff below its
singleton reward, up to the opponents' one-stage absorption.

For a nested sequence of actual profiles, vanishing opponent absorption for
the fixed observer makes that error vanish. Every sufficiently late reset
parent is separated from the singleton reward by half the fixed debt floor.
Every exact root against that child's literal payoff then supplies the same
quantitative debt drop and absorption floor.

The local exit does not require payoff convergence. Separately, summable
marginal hazards yield a simultaneous payoff limit, separated from the
singleton reward by the full debt floor when resets are cofinal. Neither
result regenerates the nested source sequence after the exact prefix.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Immediate Quit by `who` attains the complete behavioral unilateral cap
against the displayed profile. -/
def ImmediateQuitAttainsTerminalCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : Prop :=
  quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
    quittingContinuationBestResponseValue reward profile who

/-- The fixed total-debt drop and absorption floors used by the reset exit
are both strictly positive. -/
theorem fixedDebtFloor_exactPrefixDrop_and_absorptionFloors_pos
    {M debtFloor : ℝ} (hM : 0 < M) (hdebtFloor : 0 < debtFloor) :
    0 < min debtFloor
        (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M))) ∧
      0 < min 1 (debtFloor / (16 * M)) := by
  constructor <;> positivity

/-- An attained immediate-Quit cap turns literal terminal debt into a
singleton-wall inequality, with only the opponents' root absorption as an
error. -/
theorem debtFloor_sub_four_mul_opponentAbsorption_le_singletonGap_of_immediateQuitCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M debtFloor : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcap : ImmediateQuitAttainsTerminalCap reward
      (quittingRootThenContinuationProfile reward root continuation) who)
    (hdebt : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingRootThenContinuationProfile reward root continuation) who) :
    debtFloor - 4 * M * quittingRootOpponentAbsorptionMass root who ≤
      reward (quittingSingletonTerminal who) who -
        quittingTerminalPayoff reward continuation who := by
  have hidentity :=
    quittingTerminalDeviationDebt_rootThen_eq_continue_mul_endpointDifference_of_quitZeroCap
      reward root continuation who hcap
  let endpoint := quittingRootEndpointDifference reward
    (fun player => quittingTerminalPayoff reward continuation player) root who
  let ownContinue := (root who false).toReal
  have hcontinueNonneg : 0 ≤ ownContinue := ENNReal.toReal_nonneg
  have hcontinueLe : ownContinue ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one false)
  have hproduct : debtFloor ≤ ownContinue * endpoint := by
    simpa [ownContinue, endpoint] using hidentity ▸ hdebt
  have hendpointNonneg : 0 ≤ endpoint := by
    by_contra hnegative
    have hproductNonpos : ownContinue * endpoint ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcontinueNonneg (le_of_not_ge hnegative)
    linarith
  have hendpoint : debtFloor ≤ endpoint := by
    have hscaled : ownContinue * endpoint ≤ endpoint :=
      mul_le_of_le_one_left hendpointNonneg hcontinueLe
    exact hproduct.trans hscaled
  have hwall := singletonGap_ge_quittingRootEndpointDifference_sub_four_mul
    reward continuation root who hreward
  change endpoint - 4 * M * quittingRootOpponentAbsorptionMass root who ≤
    reward (quittingSingletonTerminal who) who -
      quittingTerminalPayoff reward continuation who at hwall
  linarith

/-- Vanishing opponent absorption for the fixed observer makes every
sufficiently late immediate-Quit cap reset cross half of the fixed singleton
wall. -/
theorem eventually_terminalPayoff_le_singleton_sub_half_at_immediateQuitCapReset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (who : ι) {M debtFloor : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hopponentAbsorptionZero : Tendsto (fun time =>
      quittingRootOpponentAbsorptionMass (roots time) who) atTop (nhds 0))
    (hdebt : ∀ᶠ time in atTop, debtFloor ≤
      quittingTerminalDeviationDebt reward (profiles time) who) :
    ∀ᶠ time in atTop,
      ImmediateQuitAttainsTerminalCap reward (profiles (time + 1)) who →
      quittingTerminalPayoff reward (profiles time) who ≤
        reward (quittingSingletonTerminal who) who - debtFloor / 2 := by
  have hscaledZero : Tendsto (fun time =>
      4 * M * quittingRootOpponentAbsorptionMass (roots time) who)
      atTop (nhds 0) := by
    simpa using hopponentAbsorptionZero.const_mul (4 * M)
  have hsmall : ∀ᶠ time in atTop,
      4 * M * quittingRootOpponentAbsorptionMass (roots time) who <
        debtFloor / 2 :=
    hscaledZero.eventually (Iio_mem_nhds (by linarith))
  have hdebtNext : ∀ᶠ time in atTop, debtFloor ≤
      quittingTerminalDeviationDebt reward (profiles (time + 1)) who :=
    (tendsto_add_atTop_nat 1).eventually hdebt
  filter_upwards [hsmall, hdebtNext] with time hsmallTime hdebtTime
  intro hcap
  have hcapAtPrefix : ImmediateQuitAttainsTerminalCap reward
      (quittingRootThenContinuationProfile reward (roots time)
        (profiles time)) who := by
    simpa only [← hnested time] using hcap
  have hdebtAtPrefix : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingRootThenContinuationProfile reward (roots time)
        (profiles time)) who := by
    simpa only [← hnested time] using hdebtTime
  have hwall :=
    debtFloor_sub_four_mul_opponentAbsorption_le_singletonGap_of_immediateQuitCap
      reward (roots time) (profiles time) who hdebtFloor hreward
        hcapAtPrefix hdebtAtPrefix
  linarith

/-- Every exact root against a sufficiently late reset parent's actual payoff
gives fixed debt-drop and absorption floors when the observer's opponent
absorption tends to zero. -/
theorem eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (who : ι) {M debtFloor : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hopponentAbsorptionZero : Tendsto (fun time =>
      quittingRootOpponentAbsorptionMass (roots time) who) atTop (nhds 0))
    (hdebt : ∀ᶠ time in atTop, debtFloor ≤
      quittingTerminalDeviationDebt reward (profiles time) who) :
    ∀ᶠ time in atTop,
      ImmediateQuitAttainsTerminalCap reward (profiles (time + 1)) who →
      ∀ exactRoot : ι → PMF Bool,
        IsεQuittingRootNash reward
            (fun player => quittingTerminalPayoff reward (profiles time) player)
            0 exactRoot →
        min debtFloor
              (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M))) ≤
            quittingTerminalDebtSum reward (profiles time) -
              quittingTerminalDebtSum reward
                (quittingRootThenContinuationProfile reward exactRoot
                  (profiles time)) ∧
          min 1 (debtFloor / (16 * M)) ≤
              quittingRootAbsorptionMass exactRoot := by
  have hwall :=
    eventually_terminalPayoff_le_singleton_sub_half_at_immediateQuitCapReset
      reward profiles roots who hdebtFloor hreward hnested
        hopponentAbsorptionZero hdebt
  have hdebtNow := hdebt
  filter_upwards [hwall, hdebtNow] with time hwallTime hdebtTime
  intro hcap exactRoot hnash
  have hchildPair : quittingTerminalSemanticPair reward (profiles time) ∈
      quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨profiles time, rfl⟩
  have hexit :=
    quittingTerminalSemanticPrefix_debtDrop_and_minAbsorption_of_carrier
      reward (quittingTerminalSemanticPair reward (profiles time)) exactRoot
        who hchildPair (half_pos hdebtFloor) hreward
        (abs_quittingTerminalPayoff_le reward (profiles time) who hreward)
        hdebtTime (hwallTime hcap) hnash
  have hdrop : min debtFloor
        (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M))) ≤
      quittingTerminalDebtSum reward (profiles time) -
        quittingTerminalDebtSum reward
          (quittingRootThenContinuationProfile reward exactRoot
            (profiles time)) := by
    have hconstant :
        min debtFloor
            (min (debtFloor / 2 / 2)
              (debtFloor / 2 * debtFloor / (8 * M))) =
          min debtFloor
            (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M))) := by
      congr 2 <;> ring
    rw [hconstant] at hexit
    change min debtFloor
          (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M))) ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (profiles time)) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward exactRoot
                (profiles time)))
    rw [quittingTerminalSemanticPair_rootThenContinuation]
    exact hexit.2.1
  have habsorption : min 1 (debtFloor / (16 * M)) ≤
      quittingRootAbsorptionMass exactRoot := by
    have hconstant : debtFloor / 2 / (8 * M) =
        debtFloor / (16 * M) := by ring
    rw [← hconstant]
    exact hexit.2.2
  exact ⟨hdrop, habsorption⟩

/-- Cofinal resets retain the every-exact-root exit when the observer's
opponent absorption tends to zero. -/
theorem frequently_every_exactRoot_has_debtDrop_and_absorption_of_frequently_immediateQuitCapReset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (who : ι) {M debtFloor : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hopponentAbsorptionZero : Tendsto (fun time =>
      quittingRootOpponentAbsorptionMass (roots time) who) atTop (nhds 0))
    (hdebt : ∀ᶠ time in atTop, debtFloor ≤
      quittingTerminalDeviationDebt reward (profiles time) who)
    (hreset : ∃ᶠ time in atTop,
      ImmediateQuitAttainsTerminalCap reward (profiles (time + 1)) who) :
    ∃ᶠ time in atTop,
      ∀ exactRoot : ι → PMF Bool,
        IsεQuittingRootNash reward
            (fun player => quittingTerminalPayoff reward (profiles time) player)
            0 exactRoot →
        min debtFloor
              (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M))) ≤
            quittingTerminalDebtSum reward (profiles time) -
              quittingTerminalDebtSum reward
                (quittingRootThenContinuationProfile reward exactRoot
                  (profiles time)) ∧
          min 1 (debtFloor / (16 * M)) ≤
            quittingRootAbsorptionMass exactRoot := by
  have hexit :=
    eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset
      reward profiles roots who hdebtFloor hreward hnested
        hopponentAbsorptionZero hdebt
  exact (hreset.and_eventually hexit).mono fun _ hboth => hboth.2 hboth.1

/-- A supplied carrier-wide debt lower bound gives the same fixed
off-minimum conclusion when the observer's opponent absorption tends to zero. -/
theorem eventually_resetChild_totalDebt_ge_minimum_add_fixedDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (who : ι) {M debtFloor minimumDebt : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hopponentAbsorptionZero : Tendsto (fun time =>
      quittingRootOpponentAbsorptionMass (roots time) who) atTop (nhds 0))
    (hdebt : ∀ᶠ time in atTop, debtFloor ≤
      quittingTerminalDeviationDebt reward (profiles time) who)
    (hminimum : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum pair) :
    ∀ᶠ time in atTop,
      ImmediateQuitAttainsTerminalCap reward (profiles (time + 1)) who →
        minimumDebt +
            min debtFloor
              (min (debtFloor / 4) (debtFloor ^ 2 / (16 * M))) ≤
          quittingTerminalDebtSum reward (profiles time) := by
  have hexit :=
    eventually_every_exactRoot_has_debtDrop_and_absorption_at_immediateQuitCapReset
      reward profiles roots who hdebtFloor hreward hnested
        hopponentAbsorptionZero hdebt
  filter_upwards [hexit] with time hexitTime
  intro hcap
  obtain ⟨exactRoot, hnash⟩ := exists_isZeroQuittingRootNash
    (reward := reward)
    (fun player => quittingTerminalPayoff reward (profiles time) player)
  have hdrop := (hexitTime hcap exactRoot hnash).1
  have hprefixed : quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward exactRoot
          (profiles time)) ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨quittingRootThenContinuationProfile reward exactRoot
      (profiles time), rfl⟩
  have hminimumPrefix := hminimum _ hprefixed
  change minimumDebt ≤ quittingTerminalDebtSum reward
      (quittingRootThenContinuationProfile reward exactRoot
        (profiles time)) at hminimumPrefix
  linarith

/-- Cofinal immediate-Quit cap resets put the limit of a supplied nested
actual-payoff sequence below the resetting player's singleton reward by the
full fixed debt floor. -/
theorem exists_nestedPayoffLimit_le_singleton_sub_debtFloor_of_cofinal_quitCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (who : ι) {M debtFloor : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hhazard : Summable (fun time =>
      ∑ player, ((roots time player) true).toReal))
    (hdebt : ∀ᶠ time in atTop, debtFloor ≤
      quittingTerminalDeviationDebt reward (profiles time) who)
    (hreset : ∃ᶠ time in atTop,
      ImmediateQuitAttainsTerminalCap reward (profiles (time + 1)) who) :
    ∃ limit : Payoff ι,
      (∀ player, Tendsto
        (fun time => quittingTerminalPayoff reward (profiles time) player)
        atTop (nhds (limit player))) ∧
      limit who ≤
        reward (quittingSingletonTerminal who) who - debtFloor := by
  let value : ℕ → Payoff ι := fun time player =>
    quittingTerminalPayoff reward (profiles time) player
  have hvalueNext : ∀ time, value (time + 1) =
      quittingRootSuccessorPayoff reward (value time) (roots time) := by
    intro time
    funext player
    simp only [value, hnested time,
      quittingTerminalPayoff_rootThenContinuation_eq]
    rfl
  have habsorptionSummable : Summable (fun time =>
      quittingRootAbsorptionMass (roots time)) := by
    apply Summable.of_nonneg_of_le
      (fun time => quittingRootAbsorptionMass_nonneg (roots time))
      (fun time => quittingRootAbsorptionMass_le_sum_quitProbability
        (roots time))
      hhazard
  have hcoordinate : ∀ player, ∃ coordinateLimit : ℝ,
      Tendsto (fun time => value time player) atTop (nhds coordinateLimit) := by
    intro player
    have hincrements : Summable (fun time =>
        |value (time + 1) player - value time player|) := by
      apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
        (fun time => ?_)
        (habsorptionSummable.mul_left (2 * M))
      rw [hvalueNext time]
      exact abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
        reward (value time) (roots time) player M hreward
          (abs_quittingTerminalPayoff_le reward (profiles time) player hreward)
    have hdist : Summable (fun time =>
        dist (value time player) (value (time + 1) player)) := by
      simpa [Real.dist_eq, abs_sub_comm] using hincrements
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose limit hlimit using hcoordinate
  refine ⟨limit, ?_, ?_⟩
  · intro player
    simpa only [value] using hlimit player
  · have htotalZero : Tendsto (fun time =>
        ∑ player, ((roots time player) true).toReal)
        atTop (nhds 0) := hhazard.tendsto_atTop_zero
    have hopponentZero : Tendsto (fun time =>
        quittingRootOpponentAbsorptionMass (roots time) who)
        atTop (nhds 0) := by
      apply squeeze_zero
      · intro time
        exact quittingRootOpponentAbsorptionMass_nonneg (roots time) who
      · intro time
        exact (quittingRootOpponentAbsorptionMass_le_absorptionMass
          (roots time) who).trans
            (quittingRootAbsorptionMass_le_sum_quitProbability (roots time))
      · exact htotalZero
    have herrorZero : Tendsto (fun time =>
        4 * M * quittingRootOpponentAbsorptionMass (roots time) who)
        atTop (nhds 0) := by
      simpa using hopponentZero.const_mul (4 * M)
    have hrightLimit : Tendsto (fun time =>
        reward (quittingSingletonTerminal who) who - debtFloor +
          4 * M * quittingRootOpponentAbsorptionMass (roots time) who)
        atTop
        (nhds (reward (quittingSingletonTerminal who) who - debtFloor)) := by
      simpa using
        (tendsto_const_nhds.add herrorZero)
    have hdebtNext : ∀ᶠ time in atTop, debtFloor ≤
        quittingTerminalDeviationDebt reward (profiles (time + 1)) who :=
      (tendsto_add_atTop_nat 1).eventually hdebt
    have hwall : ∀ᶠ time in atTop,
        ImmediateQuitAttainsTerminalCap reward (profiles (time + 1)) who →
          value time who ≤
            reward (quittingSingletonTerminal who) who - debtFloor +
              4 * M * quittingRootOpponentAbsorptionMass
                (roots time) who := by
      filter_upwards [hdebtNext] with time hdebtTime
      intro hcap
      have hcapAtPrefix : ImmediateQuitAttainsTerminalCap reward
          (quittingRootThenContinuationProfile reward (roots time)
            (profiles time)) who := by
        simpa only [← hnested time] using hcap
      have hdebtAtPrefix : debtFloor ≤ quittingTerminalDeviationDebt reward
          (quittingRootThenContinuationProfile reward (roots time)
            (profiles time)) who := by
        simpa only [← hnested time] using hdebtTime
      have hraw :=
        debtFloor_sub_four_mul_opponentAbsorption_le_singletonGap_of_immediateQuitCap
          reward (roots time) (profiles time) who hdebtFloor hreward
            hcapAtPrefix hdebtAtPrefix
      dsimp only [value]
      linarith
    have hfrequentWall : ∃ᶠ time in atTop,
        value time who ≤
          reward (quittingSingletonTerminal who) who - debtFloor +
            4 * M * quittingRootOpponentAbsorptionMass
              (roots time) who :=
      (hreset.and_eventually hwall).mono fun _ hboth => hboth.2 hboth.1
    by_contra hnot
    have hstrict :
        reward (quittingSingletonTerminal who) who - debtFloor < limit who :=
      lt_of_not_ge hnot
    have hdifference : Tendsto (fun time =>
        (reward (quittingSingletonTerminal who) who - debtFloor +
            4 * M * quittingRootOpponentAbsorptionMass (roots time) who) -
          value time who)
        atTop
        (nhds ((reward (quittingSingletonTerminal who) who - debtFloor) -
          limit who)) :=
      hrightLimit.sub (hlimit who)
    have hnegative : ∀ᶠ time in atTop,
        (reward (quittingSingletonTerminal who) who - debtFloor +
            4 * M * quittingRootOpponentAbsorptionMass (roots time) who) -
          value time who < 0 :=
      (tendsto_order.1 hdifference).2 0 (by linarith)
    obtain ⟨time, hle, hlt⟩ :=
      (hfrequentWall.and_eventually hnegative).exists
    linarith

end GameTheory
