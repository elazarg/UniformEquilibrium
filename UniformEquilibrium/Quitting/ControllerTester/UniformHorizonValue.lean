/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.ControllerTester.FiniteHorizonExploitability
import UniformEquilibrium.Quitting.ControllerTester.ControllerValue

/-!
# Exact offline uniform-horizon controller value

For a fixed behavioral profile, the horizon tester may choose a fresh player
and complete behavioral replacement at every horizon.  The profile's offline
value is the infimum over thresholds of the supremum over all later horizons.
Its exact limit is the corresponding terminal semantic loss.

Taking the infimum over profiles only after this pointwise equality identifies
the literal offline value with the compact semantic controller value.  No
interchange of a profile infimum with a horizon limit is used.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Fixed-target loss at one finite horizon, including the full behavioral
replacement supremum at that horizon. -/
def quittingFiniteHorizonTargetLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (horizon : ℕ) : ℝ :=
  max
    ‖(fun who => (quittingGame reward).finiteAveragePayoff none horizon
        profile who) - target‖
    (quittingFiniteHorizonExploitability reward profile horizon)

omit [DecidableEq ι] [Nonempty ι] in
/-- The finite-horizon prescribed payoff vector converges to the terminal
payoff vector of the fixed profile. -/
theorem tendsto_quittingFiniteAveragePayoffVector
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    Tendsto
      (fun horizon who =>
        (quittingGame reward).finiteAveragePayoff none horizon profile who)
      atTop (nhds (fun who => quittingTerminalPayoff reward profile who)) := by
  rw [tendsto_pi_nhds]
  exact fun who => tendsto_finiteAveragePayoff_quittingGame reward profile who

/-- For one fixed controller profile, the complete finite-horizon loss tends
to its terminal semantic loss. -/
theorem tendsto_quittingFiniteHorizonTargetLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    Tendsto (quittingFiniteHorizonTargetLoss reward target profile) atTop
      (nhds (quittingControllerTargetLoss target
        (quittingTerminalSemanticPair reward profile))) := by
  unfold quittingFiniteHorizonTargetLoss quittingControllerTargetLoss
  have hpayoff := tendsto_quittingFiniteAveragePayoffVector reward profile
  have htarget : Tendsto (fun _ : ℕ => target) atTop (nhds target) :=
    tendsto_const_nhds
  have hdelivery : Tendsto (fun horizon =>
      ‖(fun who => (quittingGame reward).finiteAveragePayoff none horizon
        profile who) - target‖) atTop
      (nhds ‖(fun who => quittingTerminalPayoff reward profile who) - target‖) :=
    (hpayoff.sub htarget).norm
  have hexploitability :=
    tendsto_quittingFiniteHorizonExploitability reward profile
  have hpairCarrier : quittingTerminalSemanticPair reward profile ∈
      quittingTerminalSemanticCarrier reward :=
    subset_closure ⟨profile, rfl⟩
  rw [quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
    reward hpairCarrier]
  change Tendsto _ atTop (nhds (max
    ‖(fun who => quittingTerminalPayoff reward profile who) - target‖
    (quittingTerminalExploitability reward profile)))
  exact hdelivery.max hexploitability

private def realTailSupremum (sequence : ℕ → ℝ) (start : ℕ) : ℝ :=
  ⨆ horizon : Set.Ici start, sequence horizon

private theorem bddAbove_realTailSupremum_range
    (sequence : ℕ → ℝ) (hbounded : BddAbove (Set.range sequence))
    (start : ℕ) :
    BddAbove (Set.range (fun horizon : Set.Ici start => sequence horizon)) := by
  apply hbounded.mono
  rintro _ ⟨horizon, rfl⟩
  exact ⟨horizon.1, rfl⟩

private theorem antitone_realTailSupremum
    (sequence : ℕ → ℝ) (hbounded : BddAbove (Set.range sequence)) :
    Antitone (realTailSupremum sequence) := by
  intro first second hle
  unfold realTailSupremum
  apply ciSup_le
  intro horizon
  exact le_ciSup (bddAbove_realTailSupremum_range sequence hbounded first)
    ⟨horizon.1, hle.trans horizon.2⟩

private theorem tendsto_realTailSupremum_of_tendsto
    (sequence : ℕ → ℝ) (limit : ℝ)
    (hlimit : Tendsto sequence atTop (nhds limit)) :
    Tendsto (realTailSupremum sequence) atTop (nhds limit) := by
  have hbounded := hlimit.bddAbove_range
  rw [Metric.tendsto_atTop] at hlimit ⊢
  intro error herror
  obtain ⟨threshold, hthreshold⟩ :=
    hlimit (error / 2) (half_pos herror)
  refine ⟨threshold, fun start hstart => ?_⟩
  have hupper : realTailSupremum sequence start ≤ limit + error / 2 := by
    unfold realTailSupremum
    apply ciSup_le
    intro horizon
    have hclose := hthreshold horizon.1 (hstart.trans horizon.2)
    rw [Real.dist_eq, abs_lt] at hclose
    linarith
  have hself : sequence start ≤ realTailSupremum sequence start := by
    exact le_ciSup
      (bddAbove_realTailSupremum_range sequence hbounded start)
      ⟨start, Set.mem_Ici.mpr le_rfl⟩
  have hlower : limit - error / 2 < sequence start := by
    have hclose := hthreshold start hstart
    rw [Real.dist_eq, abs_lt] at hclose
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem iInf_realTailSupremum_eq_of_tendsto
    (sequence : ℕ → ℝ) (limit : ℝ)
    (hlimit : Tendsto sequence atTop (nhds limit)) :
    (⨅ start : ℕ, realTailSupremum sequence start) = limit := by
  have hantitone :=
    antitone_realTailSupremum sequence hlimit.bddAbove_range
  have hbelow : BddBelow (Set.range (realTailSupremum sequence)) := by
    obtain ⟨lower, hlower⟩ := hlimit.bddBelow_range
    refine ⟨lower, ?_⟩
    rintro _ ⟨start, rfl⟩
    exact (hlower ⟨start, rfl⟩).trans
      (le_ciSup
        (bddAbove_realTailSupremum_range
          sequence hlimit.bddAbove_range start)
        ⟨start, Set.mem_Ici.mpr le_rfl⟩)
  exact tendsto_nhds_unique
    (tendsto_atTop_ciInf hantitone hbelow)
    (tendsto_realTailSupremum_of_tendsto sequence limit hlimit)

/-- Literal fixed-profile offline value: first choose a threshold, then allow
the tester to choose any later horizon. -/
def quittingUniformHorizonTargetProfileValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  ⨅ start : ℕ, ⨆ horizon : Set.Ici start,
    quittingFiniteHorizonTargetLoss reward target profile horizon

/-- The exact infimum-of-tail-suprema for one fixed profile is its terminal
semantic loss.  Horizon-dependent deviations remain inside every term. -/
theorem quittingUniformHorizonTargetProfileValue_eq_terminalLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingUniformHorizonTargetProfileValue reward target profile =
      quittingControllerTargetLoss target
        (quittingTerminalSemanticPair reward profile) := by
  exact iInf_realTailSupremum_eq_of_tendsto _ _
    (tendsto_quittingFiniteHorizonTargetLoss reward target profile)

/-- Original offline controller--tester value: the controller chooses one
behavioral profile before its threshold and the tester's later horizons. -/
def quittingUniformHorizonTargetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) : ℝ :=
  sInf (Set.range fun profile : (quittingGame reward).BehaviorProfile =>
    quittingUniformHorizonTargetProfileValue reward target profile)

/-- The literal offline uniform-horizon controller value is exactly the
compact semantic value `W_r(v)`.  The proof uses the fixed-profile equality
before taking the profile infimum, so no quantifier interchange is hidden. -/
theorem quittingUniformHorizonTargetValue_eq_controllerTargetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    quittingUniformHorizonTargetValue reward target =
      quittingControllerTargetValue reward target := by
  have hprofileNonneg : ∀ profile : (quittingGame reward).BehaviorProfile,
      0 ≤ quittingUniformHorizonTargetProfileValue reward target profile := by
    intro profile
    rw [quittingUniformHorizonTargetProfileValue_eq_terminalLoss]
    exact le_max_of_le_left (norm_nonneg _)
  have hprofileBdd : BddBelow
      (Set.range fun profile : (quittingGame reward).BehaviorProfile =>
        quittingUniformHorizonTargetProfileValue reward target profile) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨profile, rfl⟩
    exact hprofileNonneg profile
  apply le_antisymm
  · let minimizer := quittingControllerTargetMinimizer reward target
    have hminimizer : minimizer ∈ quittingTerminalSemanticCarrier reward :=
      quittingControllerTargetMinimizer_mem reward target
    obtain ⟨profiles, hprofiles⟩ :=
      exists_terminalProfile_sequence_tendsto_semanticPair
        reward minimizer hminimizer
    have hloss : Tendsto
        (fun index => quittingControllerTargetLoss target
          (quittingTerminalSemanticPair reward (profiles index)))
        atTop (nhds (quittingControllerTargetValue reward target)) := by
      have hcontinuous :=
        ((continuous_quittingControllerTargetLoss target).tendsto minimizer).comp
          hprofiles
      exact hcontinuous
    have hinfLe : ∀ index,
        quittingUniformHorizonTargetValue reward target ≤
          quittingControllerTargetLoss target
            (quittingTerminalSemanticPair reward (profiles index)) := by
      intro index
      unfold quittingUniformHorizonTargetValue
      rw [← quittingUniformHorizonTargetProfileValue_eq_terminalLoss]
      exact csInf_le hprofileBdd ⟨profiles index, rfl⟩
    exact isClosed_Ici.mem_of_tendsto hloss
      (Filter.Eventually.of_forall hinfLe)
  · unfold quittingUniformHorizonTargetValue
    apply le_csInf
    · exact ⟨_, quittingAlwaysContinueProfile reward, rfl⟩
    · rintro _ ⟨profile, rfl⟩
      change quittingControllerTargetValue reward target ≤
        quittingUniformHorizonTargetProfileValue reward target profile
      rw [quittingUniformHorizonTargetProfileValue_eq_terminalLoss]
      exact quittingControllerTargetMinimizer_isMinimum reward target
        (subset_closure ⟨profile, rfl⟩)

/-- Choosing the payoff coordinate of the target-free carrier minimizer
optimizes the literal offline uniform-horizon value exactly. -/
theorem quittingUniformHorizonTargetValue_at_targetFreeMinimizer_eq_testerValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingUniformHorizonTargetValue reward
        (quittingControllerTesterMinimizer reward).1 =
      quittingControllerTesterValue reward := by
  rw [quittingUniformHorizonTargetValue_eq_controllerTargetValue,
    quittingControllerTargetValue_at_minimizer_eq_targetFree]

/-- The target-free controller--tester value lower-bounds the literal offline
uniform-horizon value at every fixed target. -/
theorem quittingControllerTesterValue_le_uniformHorizonTargetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    quittingControllerTesterValue reward ≤
      quittingUniformHorizonTargetValue reward target := by
  rw [quittingUniformHorizonTargetValue_eq_controllerTargetValue]
  exact quittingControllerTesterValue_le_targetValue reward target

end GameTheory
