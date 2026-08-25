/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualProfileTerminalGapPaidCap

/-!
# No uniform paid-cap descent step near the minimum fiber

Carrier density does more than produce one chosen sequence of asymptotically
inert paid cap ports.  At every positive scale there is one actual full-gap
source, arbitrarily close to the global minimum, for which *every* paid cap
port has small complete absorption, small cap displacement, and small total
semantic-debt drop.  The terminal gap leaves only quantitative descent or a
literal inert stall at each such port.

Consequently, changing the summable-port selector cannot recover a uniform
positive real-valued descent step near the minimum fiber.  This does not
attain the minimum carrier point, choose an inert port, or supply a
well-founded rank with nonuniform step sizes.
-/

noncomputable section

namespace GameTheory

open Filter

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
variable {gain : ℝ}

/-- At any prescribed positive scales, one literal full-gap source near the
global minimum makes all of its paid cap ports small simultaneously.  The
universal quantifier over `actual` is the key point: selecting a different
paid row or summable port cannot restore a fixed positive descent step. -/
theorem HasTerminalExploitabilityGap.exists_profile_all_paidCapPorts_small
    (exploit : HasTerminalExploitabilityGap reward gain)
    (hgain : 0 < gain)
    (minimum : QuittingTerminalSemanticPair iota)
    (minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (minimum_le : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (debtError absorptionError displacementError : ℝ)
    (hdebtError : 0 < debtError)
    (habsorptionError : 0 < absorptionError)
    (hdisplacementError : 0 < displacementError) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      Nonempty (QuittingActualProfileTerminalGapPaidCapPort
        reward minimum profile gain) ∧
      ∀ actual : QuittingActualProfileTerminalGapPaidCapPort
          reward minimum profile gain,
        actual.source.initialDebt -
              quittingTerminalSemanticDebtSum actual.port.semanticPort.limit <
            debtError ∧
          actual.source.totalAbsorption < absorptionError ∧
          actual.source.capDisplacement actual.port < displacementError ∧
          (actual.source.QuantitativeDebtDescent actual.port ∨
            actual.source.InertStall actual.port) := by
  let rewardScale : ℝ := 2 * quittingRewardBound reward + 1
  have hrewardScale : 0 < rewardScale := by
    have hrewardBound := quittingRewardBound_nonneg reward
    dsimp only [rewardScale]
    linarith
  let motionError : ℝ := displacementError / rewardScale
  have hmotionError : 0 < motionError :=
    div_pos hdisplacementError hrewardScale
  let chargeError : ℝ := min absorptionError motionError
  have hchargeError : 0 < chargeError :=
    lt_min habsorptionError hmotionError
  let sourceError : ℝ := min debtError
    (quittingTerminalSemanticDebtSum minimum * chargeError)
  have hsourceError : 0 < sourceError := by
    dsimp only [sourceError]
    exact lt_min hdebtError (mul_pos minimum_pos hchargeError)
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair
      reward minimum minimum_mem
  have hdebtTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n)))
      atTop (nhds (quittingTerminalSemanticDebtSum minimum)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hprofiles
  have hnearEventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) <
        quittingTerminalSemanticDebtSum minimum + sourceError :=
    hdebtTendsto.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hsourceError))
  obtain ⟨n, hnear⟩ := hnearEventually.exists
  let profile := profiles n
  have hactual : Nonempty (QuittingActualProfileTerminalGapPaidCapPort
      reward minimum profile gain) :=
    exploit.nonempty_actualProfilePaidCapPort hgain minimum minimum_le
      minimum_pos profile
  refine ⟨profile, hactual, ?_⟩
  intro actual
  have hinitial : actual.source.initialDebt =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by
    rw [QuittingPaidCapLiftedSource.initialDebt, actual.source_profile]
  have hsourceMinimum :
      quittingTerminalSemanticDebtSum actual.source.minimum =
        quittingTerminalSemanticDebtSum minimum :=
    congrArg quittingTerminalSemanticDebtSum actual.source_minimum
  have hexcess : actual.source.initialDebt -
        quittingTerminalSemanticDebtSum minimum < sourceError := by
    rw [hinitial]
    dsimp only [profile]
    linarith
  have hlimitLower : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum actual.port.semanticPort.limit :=
    minimum_le actual.port.semanticPort.limit
      actual.port.semanticPort.limit_mem
  have hdrop : actual.source.initialDebt -
        quittingTerminalSemanticDebtSum actual.port.semanticPort.limit <
      debtError := by
    have hsourceErrorLe : sourceError ≤ debtError := min_le_left _ _
    linarith
  have habsorptionCharge :=
    actual.source.minimum_mul_totalAbsorption_le_excess actual.port
  rw [hsourceMinimum] at habsorptionCharge
  have hsourceErrorLeCharge : sourceError ≤
      quittingTerminalSemanticDebtSum minimum * chargeError :=
    min_le_right _ _
  have habsorptionSmall : actual.source.totalAbsorption < chargeError := by
    nlinarith
  have habsorption : actual.source.totalAbsorption < absorptionError :=
    habsorptionSmall.trans_le (min_le_left _ _)
  have habsorptionMotion :
      actual.source.totalAbsorption < motionError :=
    habsorptionSmall.trans_le (min_le_right _ _)
  have hscaledMotion : rewardScale * actual.source.totalAbsorption <
      displacementError := by
    have hproduct := (lt_div_iff₀ hrewardScale).mp
      (show actual.source.totalAbsorption <
        displacementError / rewardScale by
        simpa only [motionError] using habsorptionMotion)
    simpa [mul_comm] using hproduct
  have hcapBound :=
    actual.source.capDisplacement_le_two_mul_totalAbsorption actual.port
  have hscaleBound : 2 * quittingRewardBound reward *
        actual.source.totalAbsorption ≤
      rewardScale * actual.source.totalAbsorption := by
    exact mul_le_mul_of_nonneg_right (by
      dsimp only [rewardScale]
      linarith) actual.source.totalAbsorption_nonneg
  have hdisplacement :
      actual.source.capDisplacement actual.port < displacementError :=
    hcapBound.trans_lt (hscaleBound.trans_lt hscaledMotion)
  exact ⟨hdrop, habsorption, hdisplacement,
    actual.quantitativeDebtDescent_or_inertStall hgain exploit⟩

/-- No rule can assign every literal source a paid cap port with one fixed
positive total-debt drop.  This rules out uniform real-valued descent as the
missing regeneration mechanism; nonuniform or genuinely well-founded ranks
are not addressed. -/
theorem HasTerminalExploitabilityGap.not_uniformPositivePaidCapDebtDropSelection
    (exploit : HasTerminalExploitabilityGap reward gain)
    (hgain : 0 < gain)
    (minimum : QuittingTerminalSemanticPair iota)
    (minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (minimum_le : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (step : ℝ) (hstep : 0 < step) :
    ¬ ∀ profile : (quittingGame reward).BehaviorProfile,
      ∃ actual : QuittingActualProfileTerminalGapPaidCapPort
          reward minimum profile gain,
        step ≤ actual.source.initialDebt -
          quittingTerminalSemanticDebtSum actual.port.semanticPort.limit := by
  intro hselection
  obtain ⟨profile, _hactual, hall⟩ :=
    exploit.exists_profile_all_paidCapPorts_small hgain minimum minimum_mem
      minimum_le minimum_pos step 1 1 hstep (by norm_num) (by norm_num)
  obtain ⟨actual, hdrop⟩ := hselection profile
  exact (not_lt_of_ge hdrop) (hall actual).1

end GameTheory
