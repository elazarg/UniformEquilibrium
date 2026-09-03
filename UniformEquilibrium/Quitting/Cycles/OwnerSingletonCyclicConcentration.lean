/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.InteriorCyclicAbsorptionAlternatives
import UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-!
# Singleton concentration for a cyclic quitting profile

When one owner's probability of quitting during a turn is bounded below and
every opponent's probability of quitting during that turn is small, the
repeated cyclic profile concentrates on the owner's singleton terminal.  The
proof keeps the observation coordinate independent of the owner, so it gives
the whole payoff vector rather than only the owner's coordinate.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The terminal-outcome point mass on one player's singleton coalition. -/
def quittingSingletonTerminalOutcomeMass (owner : ι) :
    QuittingTerminalOutcome ι → ℝ
  | none => 0
  | some terminal => if terminal = quittingSingletonTerminal owner then 1 else 0

private def quittingTerminalCoalitionIndicatorPayoff
    (terminal : {S : Finset ι // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun outcome _ => if outcome = terminal then 1 else 0

omit [Fintype ι] in
private theorem quittingTerminalCoalitionIndicatorPayoff_abs_le_one
    (terminal outcome : {S : Finset ι // S.Nonempty}) (who : ι) :
    |quittingTerminalCoalitionIndicatorPayoff terminal outcome who| ≤ 1 := by
  simp only [quittingTerminalCoalitionIndicatorPayoff]
  split_ifs <;> norm_num

private theorem quittingTerminalOutcomeMass_cyclicBehaviorProfile_some_eq_indicatorValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {K : ℕ} (cycle : Fin K → ι → PMF Bool) (initial : Fin K)
    (terminal : {S : Finset ι // S.Nonempty}) (observer : ι) :
    quittingTerminalOutcomeMass reward
        (quittingCyclicBehaviorProfile reward cycle initial) (some terminal) =
      quittingCyclicTerminalValue
        (quittingTerminalCoalitionIndicatorPayoff terminal) cycle initial
          observer := by
  let indicator := quittingTerminalCoalitionIndicatorPayoff terminal
  let profile := quittingCyclicBehaviorProfile indicator cycle initial
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass indicator profile) observer
  have hmass : quittingAbsorbedMassLimit reward
      (quittingCyclicBehaviorProfile reward cycle initial) terminal =
        quittingAbsorbedMassLimit indicator profile terminal := by
    exact quittingAbsorbedMassLimit_reward_irrelevant reward indicator
      (quittingCyclicBehaviorProfile reward cycle initial) terminal
  change quittingAbsorbedMassLimit reward
      (quittingCyclicBehaviorProfile reward cycle initial) terminal = _
  rw [hmass]
  change quittingAbsorbedMassLimit indicator profile terminal =
    quittingTerminalPayoff indicator profile observer
  rw [← hmoment]
  unfold quittingTerminalRewardMoment quittingTerminalOutcomeReward
    quittingTerminalOutcomeMass indicator profile
  rw [Fintype.sum_option]
  simp only [Pi.zero_apply, mul_zero, zero_add, indicator,
    quittingTerminalCoalitionIndicatorPayoff]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp

/-- Forcing `owner` to Quit differs from the owner's singleton contribution
only on joint actions in which an opponent Quits.  The estimate holds at an
arbitrary observation coordinate. -/
theorem abs_quittingRootAbsorbingContribution_forcedQuit_sub_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner observer : ι) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    |quittingRootAbsorbingContribution reward
          (Function.update root owner (PMF.pure true)) observer -
        quittingRootOpponentContinueMass root owner *
          reward (quittingSingletonTerminal owner) observer| ≤
      M * quittingRootOpponentAbsorptionMass root owner := by
  have hM : 0 ≤ M :=
    (abs_nonneg (reward (quittingSingletonTerminal owner) observer)).trans
      (hreward _ _)
  let forcedRoot := Function.update root owner (PMF.pure true)
  let soloAction : ι → Bool := quittingSoloQuitAction owner
  have hpoint : quittingRootPayoff reward (0 : Payoff ι) soloAction observer =
      reward (quittingSingletonTerminal owner) observer := by
    have hnonempty : (quittingQuitters soloAction).Nonempty := by
      rw [show quittingQuitters soloAction = {owner} by
        simpa only [soloAction] using quittingQuitters_soloQuitAction owner]
      exact Finset.singleton_nonempty owner
    unfold quittingRootPayoff
    rw [dif_pos hnonempty]
    congr 1
    apply Subtype.ext
    change quittingQuitters (quittingSoloQuitAction owner) = {owner}
    simpa only [soloAction] using quittingQuitters_soloQuitAction owner
  have hpayoff : ∀ action : ι → Bool,
      |quittingRootPayoff reward (0 : Payoff ι) action observer| ≤ M := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · simpa [quittingRootPayoff, hquit] using
        hreward ⟨quittingQuitters action, hquit⟩ observer
    · simpa [quittingRootPayoff, hquit] using hM
  have hestimate := abs_expect_sub_singletonContribution_le
    (pmfPi forcedRoot) soloAction
      (fun action => quittingRootPayoff reward (0 : Payoff ι) action observer)
      (reward (quittingSingletonTerminal owner) observer) M hpoint hpayoff
  have hmass : ((pmfPi forcedRoot) soloAction).toReal =
      quittingRootOpponentContinueMass root owner := by
    simpa only [forcedRoot, soloAction,
      quittingRootOpponentContinueMass] using
      pmfPi_update_pure_true_soloQuitAction_toReal root owner
  rw [hmass] at hestimate
  simpa [forcedRoot, soloAction, quittingRootAbsorbingContribution,
    quittingRootExpectedPayoff,
    quittingRootOpponentAbsorptionMass,
    quittingRootOpponentContinueMass,
    quittingRootAbsorptionMass] using hestimate

/-- Forcing `owner` to Continue leaves an absorbing contribution only when
an opponent Quits.  The estimate holds at an arbitrary observation
coordinate. -/
theorem abs_quittingRootAbsorbingContribution_forcedContinue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner observer : ι) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    |quittingRootAbsorbingContribution reward
        (Function.update root owner (PMF.pure false)) observer| ≤
      M * quittingRootOpponentAbsorptionMass root owner := by
  simpa only [quittingRootOpponentAbsorptionMass,
    quittingRootOpponentContinueMass] using
      abs_quittingRootAbsorbingContribution_le reward
        (Function.update root owner (PMF.pure false)) observer M hreward

/-- The one-stage absorbing contribution splits through one selected
player's own Boolean marginal. -/
theorem quittingRootAbsorbingContribution_eq_ownerEndpointMix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner observer : ι) :
    quittingRootAbsorbingContribution reward root observer =
      (root owner true).toReal *
          quittingRootAbsorbingContribution reward
            (Function.update root owner (PMF.pure true)) observer +
        (root owner false).toReal *
          quittingRootAbsorbingContribution reward
            (Function.update root owner (PMF.pure false)) observer := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  conv_lhs =>
    rw [show root = Function.update root owner (root owner) by
      exact (Function.update_eq_self owner root).symm]
  rw [pmfPi_update_bind, expect_bind, expect_eq_sum, Fintype.sum_bool]

/-- One Bellman step stays close to transport toward an owner's singleton
reward.  The residual is twice the payoff bound times the probability that
some opponent of the owner Quits. -/
theorem abs_quittingRootSuccessorPayoff_sub_ownerSingleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (owner observer : ι) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    |quittingRootSuccessorPayoff reward tail root observer -
        reward (quittingSingletonTerminal owner) observer| ≤
      2 * M * quittingRootOpponentAbsorptionMass root owner +
        quittingStationaryContinueMass root *
          |tail observer -
            reward (quittingSingletonTerminal owner) observer| := by
  have hM : 0 ≤ M :=
    (abs_nonneg (reward (quittingSingletonTerminal owner) observer)).trans
      (hreward _ _)
  let quitProbability := (root owner true).toReal
  let continueProbability := (root owner false).toReal
  let opponentContinue := quittingRootOpponentContinueMass root owner
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root owner
  let singleton := reward (quittingSingletonTerminal owner) observer
  let forcedQuit := quittingRootAbsorbingContribution reward
    (Function.update root owner (PMF.pure true)) observer
  let forcedContinue := quittingRootAbsorbingContribution reward
    (Function.update root owner (PMF.pure false)) observer
  have hquitProbability : 0 ≤ quitProbability := ENNReal.toReal_nonneg
  have hcontinueProbability : 0 ≤ continueProbability := ENNReal.toReal_nonneg
  have hprobabilitySum : quitProbability + continueProbability = 1 := by
    dsimp only [quitProbability, continueProbability]
    linarith [quittingRoot_continueProbability_add_quitProbability root owner]
  have hopponentAbsorption : 0 ≤ opponentAbsorption :=
    quittingRootOpponentAbsorptionMass_nonneg root owner
  have hquit : |forcedQuit - opponentContinue * singleton| ≤
      M * opponentAbsorption := by
    exact abs_quittingRootAbsorbingContribution_forcedQuit_sub_singleton_le
      reward root owner observer hreward
  have hcontinue : |forcedContinue| ≤ M * opponentAbsorption := by
    exact abs_quittingRootAbsorbingContribution_forcedContinue_le
      reward root owner observer hreward
  have hsingleton : |singleton| ≤ M := hreward _ _
  have hmix : quittingRootAbsorbingContribution reward root observer =
      quitProbability * forcedQuit + continueProbability * forcedContinue := by
    exact quittingRootAbsorbingContribution_eq_ownerEndpointMix
      reward root owner observer
  have hjoint : quittingStationaryContinueMass root =
      opponentContinue * continueProbability := by
    exact quittingStationaryContinueMass_eq_forcedContinue_mul_own root owner
  have hcomplement : opponentContinue = 1 - opponentAbsorption := by
    exact quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root owner
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add, hmix, hjoint]
  change |quitProbability * forcedQuit + continueProbability * forcedContinue +
      opponentContinue * continueProbability * tail observer - singleton| ≤
    2 * M * opponentAbsorption +
      (opponentContinue * continueProbability) *
        |tail observer - singleton|
  have halgebra :
      quitProbability * forcedQuit + continueProbability * forcedContinue +
          opponentContinue * continueProbability * tail observer - singleton =
        quitProbability * (forcedQuit - opponentContinue * singleton) +
          continueProbability * forcedContinue -
          opponentAbsorption * singleton +
          opponentContinue * continueProbability *
            (tail observer - singleton) := by
    have hcontinueEq : continueProbability = 1 - quitProbability := by
      linarith
    rw [hcomplement]
    rw [hcontinueEq]
    ring
  rw [halgebra]
  calc
    |quitProbability * (forcedQuit - opponentContinue * singleton) +
          continueProbability * forcedContinue -
          opponentAbsorption * singleton +
          opponentContinue * continueProbability *
            (tail observer - singleton)| ≤
        quitProbability * |forcedQuit - opponentContinue * singleton| +
          continueProbability * |forcedContinue| +
          opponentAbsorption * |singleton| +
          (opponentContinue * continueProbability) *
            |tail observer - singleton| := by
      have hopponentContinue : 0 ≤ opponentContinue :=
        quittingRootOpponentContinueMass_nonneg root owner
      calc
        |quitProbability * (forcedQuit - opponentContinue * singleton) +
              continueProbability * forcedContinue -
              opponentAbsorption * singleton +
              opponentContinue * continueProbability *
                (tail observer - singleton)| ≤
            |quitProbability *
                (forcedQuit - opponentContinue * singleton) +
                continueProbability * forcedContinue -
                opponentAbsorption * singleton| +
              |opponentContinue * continueProbability *
                (tail observer - singleton)| := abs_add_le _ _
        _ ≤ (|quitProbability *
                (forcedQuit - opponentContinue * singleton) +
                continueProbability * forcedContinue| +
              |-opponentAbsorption * singleton|) +
              |opponentContinue * continueProbability *
                (tail observer - singleton)| := by
          gcongr
          simpa only [sub_eq_add_neg, neg_mul] using
            abs_add_le
              (quitProbability *
                  (forcedQuit - opponentContinue * singleton) +
                continueProbability * forcedContinue)
              (-opponentAbsorption * singleton)
        _ ≤ ((|quitProbability *
                (forcedQuit - opponentContinue * singleton)| +
              |continueProbability * forcedContinue|) +
              |-opponentAbsorption * singleton|) +
              |opponentContinue * continueProbability *
                (tail observer - singleton)| := by
          gcongr
          exact abs_add_le _ _
        _ = quitProbability *
              |forcedQuit - opponentContinue * singleton| +
            continueProbability * |forcedContinue| +
            opponentAbsorption * |singleton| +
            (opponentContinue * continueProbability) *
              |tail observer - singleton| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg,
            abs_of_nonneg hquitProbability,
            abs_of_nonneg hcontinueProbability,
            abs_of_nonneg hopponentAbsorption,
            abs_of_nonneg
              (mul_nonneg hopponentContinue hcontinueProbability)]
    _ ≤ quitProbability * (M * opponentAbsorption) +
          continueProbability * (M * opponentAbsorption) +
          opponentAbsorption * M +
          (opponentContinue * continueProbability) *
            |tail observer - singleton| := by
      gcongr
    _ = 2 * M * opponentAbsorption +
          (opponentContinue * continueProbability) *
            |tail observer - singleton| := by
      calc
        quitProbability * (M * opponentAbsorption) +
              continueProbability * (M * opponentAbsorption) +
              opponentAbsorption * M +
              opponentContinue * continueProbability *
                |tail observer - singleton| =
            (quitProbability + continueProbability) *
                (M * opponentAbsorption) +
              M * opponentAbsorption +
              opponentContinue * continueProbability *
                |tail observer - singleton| := by ring
        _ = 2 * M * opponentAbsorption +
              opponentContinue * continueProbability *
                |tail observer - singleton| := by
          rw [hprobabilitySum]
          ring

/-- If the owner has positive probability of quitting during one turn, the
terminal payoff of the repeated cycle is close to the owner's singleton
reward vector.  The numerator is the probability that some opponent Quits
during the turn; the denominator is the owner's own turn-absorption
probability. -/
theorem abs_quittingCyclicTerminalValue_sub_ownerSingleton_le
    {K : ℕ} (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (owner observer : ι) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (howner : 0 < quittingCyclicPlayerAbsorptionMass cycle owner) :
    |quittingCyclicTerminalValue reward cycle phase observer -
        reward (quittingSingletonTerminal owner) observer| ≤
      2 * M * quittingCyclicOpponentAbsorptionMass cycle owner /
        quittingCyclicPlayerAbsorptionMass cycle owner := by
  have hM : 0 ≤ M :=
    (abs_nonneg (reward (quittingSingletonTerminal owner) observer)).trans
      (hreward _ _)
  let jointContinue : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryContinueMass (cycle cyclePhase)
  let opponentContinue : Fin K → ℝ := fun cyclePhase =>
    quittingStationaryFixedOpponentsContinueMass
      (cycle cyclePhase) owner
  let residual : Fin K → ℝ := fun cyclePhase =>
    2 * M * (1 - opponentContinue cyclePhase)
  let difference : Fin K → ℝ := fun cyclePhase =>
    quittingCyclicTerminalValue reward cycle cyclePhase observer -
      reward (quittingSingletonTerminal owner) observer
  have hjointNonneg : ∀ cyclePhase, 0 ≤ jointContinue cyclePhase :=
    fun cyclePhase => quittingStationaryContinueMass_nonneg _
  have hopponentNonneg : ∀ cyclePhase, 0 ≤ opponentContinue cyclePhase :=
    fun cyclePhase =>
      quittingStationaryFixedOpponentsContinueMass_nonneg _ _
  have hopponentLeOne : ∀ cyclePhase, opponentContinue cyclePhase ≤ 1 :=
    fun cyclePhase =>
      quittingStationaryContinueMass_le_one _
  have hjointLeOpponent : ∀ cyclePhase,
      jointContinue cyclePhase ≤ opponentContinue cyclePhase :=
    fun cyclePhase =>
      quittingStationaryContinueMass_le_fixedOpponentsContinueMass _ _
  have hjointLeOwn :
      (∏ cyclePhase : Fin K, jointContinue cyclePhase) ≤
        ∏ cyclePhase : Fin K, (cycle cyclePhase owner false).toReal := by
    apply Finset.prod_le_prod
    · intro cyclePhase _
      exact hjointNonneg cyclePhase
    · intro cyclePhase _
      exact quittingStationaryContinueMass_le_ownContinueProbability
        (cycle cyclePhase) owner
  have hjointContracts : (∏ cyclePhase : Fin K,
      jointContinue cyclePhase) < 1 := by
    unfold quittingCyclicPlayerAbsorptionMass at howner
    exact hjointLeOwn.trans_lt (sub_pos.mp howner)
  have hstep : ∀ cyclePhase,
      |difference cyclePhase| ≤ residual cyclePhase +
        jointContinue cyclePhase *
          |difference (finRotate K cyclePhase)| := by
    intro cyclePhase
    have hterminal :=
      quittingCyclicTerminalValue_eq_rootSuccessorPayoff
        reward cycle cyclePhase
    have honeStep := abs_quittingRootSuccessorPayoff_sub_ownerSingleton_le
      reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K cyclePhase))
        (cycle cyclePhase) owner observer hreward
    rw [← hterminal] at honeStep
    simpa only [difference, residual, jointContinue, opponentContinue,
      quittingRootOpponentAbsorptionMass,
      quittingRootOpponentContinueMass,
      quittingRootAbsorptionMass,
      quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass] using honeStep
  have hcontraction := abs_cyclicValue_le_residualCharge_div_one_sub_prod
    jointContinue residual difference hjointNonneg hjointContracts hstep phase
  have hprefixLe : ∀ fuel,
      quittingCyclicPrefixWeight jointContinue phase fuel ≤
        quittingCyclicPrefixWeight opponentContinue phase fuel := by
    intro fuel
    unfold quittingCyclicPrefixWeight
    apply Finset.prod_le_prod
    · intro offset _
      exact hjointNonneg _
    · intro offset _
      exact hjointLeOpponent _
  have hopponentTelescope :
      (∑ offset ∈ Finset.range K,
          quittingCyclicPrefixWeight opponentContinue phase offset *
            (1 - opponentContinue
              (quittingCyclicOrbit phase offset))) =
        1 - ∏ cyclePhase : Fin K, opponentContinue cyclePhase := by
    have htelescope := Math.sum_survivalProduct_mul_one_sub
      (fun offset => opponentContinue (quittingCyclicOrbit phase offset)) 0 K
    have hfull := quittingCyclicPrefixWeight_card
      opponentContinue phase
    have htelescope' :
        (∑ offset ∈ Finset.range K,
            quittingCyclicPrefixWeight opponentContinue phase offset *
              (1 - opponentContinue
                (quittingCyclicOrbit phase offset))) =
          1 - quittingCyclicPrefixWeight opponentContinue phase K := by
      simpa only [Math.survivalProduct, Nat.zero_add,
        quittingCyclicPrefixWeight] using htelescope
    rw [hfull] at htelescope'
    exact htelescope'
  have hcharge :
      quittingCyclicResidualCharge jointContinue residual phase K ≤
        2 * M * quittingCyclicOpponentAbsorptionMass cycle owner := by
    unfold quittingCyclicResidualCharge residual
    calc
      (∑ offset ∈ Finset.range K,
          quittingCyclicPrefixWeight jointContinue phase offset *
            (2 * M *
              (1 - opponentContinue
                (quittingCyclicOrbit phase offset)))) ≤
          ∑ offset ∈ Finset.range K,
            quittingCyclicPrefixWeight opponentContinue phase offset *
              (2 * M *
                (1 - opponentContinue
                  (quittingCyclicOrbit phase offset))) := by
        apply Finset.sum_le_sum
        intro offset _
        apply mul_le_mul_of_nonneg_right (hprefixLe offset)
        exact mul_nonneg (mul_nonneg (by norm_num) hM)
          (sub_nonneg.mpr (hopponentLeOne _))
      _ = 2 * M *
          (∑ offset ∈ Finset.range K,
            quittingCyclicPrefixWeight opponentContinue phase offset *
              (1 - opponentContinue
                (quittingCyclicOrbit phase offset))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        ring
      _ = 2 * M * quittingCyclicOpponentAbsorptionMass cycle owner := by
        rw [hopponentTelescope]
        rfl
  have hopponentAbsorptionNonneg :
      0 ≤ quittingCyclicOpponentAbsorptionMass cycle owner := by
    unfold quittingCyclicOpponentAbsorptionMass
    exact sub_nonneg.mpr <| Finset.prod_le_one
      (fun cyclePhase _ => hopponentNonneg cyclePhase)
      (fun cyclePhase _ => hopponentLeOne cyclePhase)
  have hnumeratorNonneg :
      0 ≤ 2 * M * quittingCyclicOpponentAbsorptionMass cycle owner := by
    positivity
  have hdenominator :
      quittingCyclicPlayerAbsorptionMass cycle owner ≤
        1 - ∏ cyclePhase : Fin K, jointContinue cyclePhase := by
    unfold quittingCyclicPlayerAbsorptionMass
    linarith
  calc
    |quittingCyclicTerminalValue reward cycle phase observer -
        reward (quittingSingletonTerminal owner) observer| =
        |difference phase| := rfl
    _ ≤ quittingCyclicResidualCharge jointContinue residual phase K /
        (1 - ∏ cyclePhase : Fin K, jointContinue cyclePhase) := hcontraction
    _ ≤ (2 * M * quittingCyclicOpponentAbsorptionMass cycle owner) /
        (1 - ∏ cyclePhase : Fin K, jointContinue cyclePhase) := by
      exact div_le_div_of_nonneg_right hcharge (sub_nonneg.mpr hjointContracts.le)
    _ ≤ 2 * M * quittingCyclicOpponentAbsorptionMass cycle owner /
        quittingCyclicPlayerAbsorptionMass cycle owner := by
      exact div_le_div_of_nonneg_left hnumeratorNonneg howner hdenominator

/-- Uniformly positive owner absorption and vanishing opponent absorption
force every coordinate of the cyclic terminal payoff to converge to the
owner's singleton reward.  Cycle lengths and initial phases may vary. -/
theorem tendsto_quittingCyclicTerminalValue_ownerSingleton_of_absorption
    (period : ℕ → ℕ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : ∀ n, Fin (period n + 1) → ι → PMF Bool)
    (initial : ∀ n, Fin (period n + 1))
    (owner : ι) {absorptionFloor : ℝ}
    (hfloor : 0 < absorptionFloor)
    (howner : ∀ n, absorptionFloor ≤
      quittingCyclicPlayerAbsorptionMass (cycle n) owner)
    (hopponents : Filter.Tendsto (fun n =>
      quittingCyclicOpponentAbsorptionMass (cycle n) owner)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n =>
      quittingCyclicTerminalValue reward (cycle n) (initial n))
      Filter.atTop
      (nhds (fun observer =>
        reward (quittingSingletonTerminal owner) observer)) := by
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hreward : ∀ terminal who, |reward terminal who| ≤ M :=
    abs_reward_le_quittingRewardBound reward
  rw [tendsto_pi_nhds]
  intro observer
  have hbound : ∀ n,
      |quittingCyclicTerminalValue reward (cycle n) (initial n) observer -
          reward (quittingSingletonTerminal owner) observer| ≤
        2 * M * quittingCyclicOpponentAbsorptionMass (cycle n) owner /
          absorptionFloor := by
    intro n
    have hpositive : 0 <
        quittingCyclicPlayerAbsorptionMass (cycle n) owner :=
      hfloor.trans_le (howner n)
    have hraw := abs_quittingCyclicTerminalValue_sub_ownerSingleton_le
      reward (cycle n) (initial n) owner observer hreward hpositive
    have hnumerator :
        0 ≤ 2 * M * quittingCyclicOpponentAbsorptionMass (cycle n) owner := by
      have hopponent :
          0 ≤ quittingCyclicOpponentAbsorptionMass (cycle n) owner := by
        unfold quittingCyclicOpponentAbsorptionMass
        exact sub_nonneg.mpr <| Finset.prod_le_one
          (fun phase _ =>
            quittingStationaryFixedOpponentsContinueMass_nonneg _ _)
          (fun phase _ =>
            quittingStationaryContinueMass_le_one _)
      positivity
    exact hraw.trans <|
      div_le_div_of_nonneg_left hnumerator hfloor (howner n)
  have hright : Filter.Tendsto (fun n =>
      2 * M * quittingCyclicOpponentAbsorptionMass (cycle n) owner /
        absorptionFloor) Filter.atTop (nhds 0) := by
    simpa [hfloor.ne'] using
      (hopponents.const_mul (2 * M)).div_const absorptionFloor
  apply tendsto_iff_dist_tendsto_zero.mpr
  have habsolute : Filter.Tendsto (fun n =>
      |quittingCyclicTerminalValue reward (cycle n) (initial n) observer -
        reward (quittingSingletonTerminal owner) observer|)
      Filter.atTop (nhds 0) := by
    exact squeeze_zero (fun _ => abs_nonneg _) hbound hright
  simpa only [Real.dist_eq] using habsolute

/-- Uniformly positive owner absorption and vanishing opponent absorption
force the actual terminal-outcome laws of the repeated cyclic profiles to
converge coordinatewise to the point mass on the owner's singleton
coalition. Cycle lengths and initial phases may vary. -/
theorem tendsto_quittingTerminalOutcomeMass_cyclicBehaviorProfile_singleton_of_absorption
    (period : ℕ → ℕ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : ∀ n, Fin (period n + 1) → ι → PMF Bool)
    (initial : ∀ n, Fin (period n + 1))
    (owner : ι) {absorptionFloor : ℝ}
    (hfloor : 0 < absorptionFloor)
    (howner : ∀ n, absorptionFloor ≤
      quittingCyclicPlayerAbsorptionMass (cycle n) owner)
    (hopponents : Filter.Tendsto (fun n =>
      quittingCyclicOpponentAbsorptionMass (cycle n) owner)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n =>
      quittingTerminalOutcomeMass reward
        (quittingCyclicBehaviorProfile reward (cycle n) (initial n)))
      Filter.atTop (nhds (quittingSingletonTerminalOutcomeMass owner)) := by
  rw [tendsto_pi_nhds]
  have hsome : ∀ terminal, Filter.Tendsto (fun n =>
      quittingTerminalOutcomeMass reward
        (quittingCyclicBehaviorProfile reward (cycle n) (initial n))
          (some terminal)) Filter.atTop
      (nhds (quittingSingletonTerminalOutcomeMass owner (some terminal))) := by
    intro terminal
    have hpayoff :=
      tendsto_quittingCyclicTerminalValue_ownerSingleton_of_absorption
        period (quittingTerminalCoalitionIndicatorPayoff terminal) cycle
          initial owner hfloor howner
          hopponents
    have hcoordinate := tendsto_pi_nhds.mp hpayoff owner
    convert hcoordinate using 1
    · funext n
      exact
        quittingTerminalOutcomeMass_cyclicBehaviorProfile_some_eq_indicatorValue
          reward (cycle n) (initial n) terminal owner
    · simp [quittingSingletonTerminalOutcomeMass,
        quittingTerminalCoalitionIndicatorPayoff, eq_comm]
  intro outcome
  cases outcome with
  | some terminal => exact hsome terminal
  | none =>
      have hsum : Filter.Tendsto (fun n =>
          ∑ terminal, quittingTerminalOutcomeMass reward
            (quittingCyclicBehaviorProfile reward (cycle n) (initial n))
              (some terminal)) Filter.atTop (nhds 1) := by
        convert tendsto_finsetSum Finset.univ fun terminal _ => hsome terminal using 1
        simp [quittingSingletonTerminalOutcomeMass]
      have hnone : ∀ n,
          quittingTerminalOutcomeMass reward
              (quittingCyclicBehaviorProfile reward (cycle n) (initial n)) none =
            1 - ∑ terminal, quittingTerminalOutcomeMass reward
              (quittingCyclicBehaviorProfile reward (cycle n) (initial n))
                (some terminal) := by
        intro n
        have htotal := (quittingTerminalOutcomeMass_mem_stdSimplex reward
          (quittingCyclicBehaviorProfile reward (cycle n) (initial n))).2
        rw [Fintype.sum_option] at htotal
        linarith
      have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop
          (nhds 1) := tendsto_const_nhds
      have hlimit := hone.sub hsum
      convert hlimit using 1
      · funext n
        exact hnone n
      · simp [quittingSingletonTerminalOutcomeMass]

end GameTheory
