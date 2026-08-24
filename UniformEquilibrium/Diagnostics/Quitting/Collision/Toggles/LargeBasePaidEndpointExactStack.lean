/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Capacity.InfiniteOrbitConsequences
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargeBasePaidEndpointAtomDispatch
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SingletonGapFiniteCollisionBudget
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbitSegment
import UniformEquilibrium.Quitting.Projective.PunishmentFloorNearReturn
import UniformEquilibrium.Quitting.Root.SemanticExactPrefixOrbit

/-!
# Exact floor stacks at a large-base paid endpoint

The repaired stationary profile retained by the large-base handoff is an
actual terminal-semantic carrier point.  In the floor-safe arm, finite mixed
Nash existence therefore produces one literal infinite exact prefix orbit
from that same source.  This file instantiates the generic singleton-gap
collision budget on its finite truncations and records the exact payoff
near-return consumer for segments of the orbit.

The singleton-gap theorem is conditional on the selected immediate-Quit arm
and the displayed minimum-debt hypotheses.  The recurrence theorem is also a
consumer: it does not assert that charged payoff recurrence occurs.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingSingletonBaseStationaryHandoff

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner : ι} {free : Finset ι}
variable {point : mixedPolytope (quittingBinaryForm free).sig}
variable {delta terminalGap : ℝ}

/-- The literal terminal-semantic pair of the repaired stationary source. -/
def repairedSemanticSource
    (_handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingSingletonBaseRepairedProfile reward owner free point)

/-- The repaired stationary source belongs to the attainable semantic
carrier without taking any closure limit. -/
theorem repairedSemanticSource_mem_carrier
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap) :
    handoff.repairedSemanticSource ∈
      quittingTerminalSemanticCarrier reward :=
  quittingTerminalSemanticPair_mem_carrier reward _

/-- The selected exact finite stack starting at the literal repaired source. -/
def repairedExactFinitePrefix
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward :=
  quittingTerminalSemanticExactFinitePrefix reward
    handoff.repairedSemanticSource handoff.repairedSemanticSource_mem_carrier
    hfloor horizon

/-- The selected exact infinite stack starting at the literal repaired
stationary source. -/
def repairedExactInfiniteOrbit
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who) :
    QuittingPunishmentFloorInfiniteOrbit reward where
  roots time := quittingTerminalSemanticSelectedExactRoot reward
    (quittingTerminalSemanticExactPrefixOrbit reward
      handoff.repairedSemanticSource time)
  value time := (quittingTerminalSemanticExactPrefixOrbit reward
    handoff.repairedSemanticSource time).1
  value_mem := by
    intro time
    have hpair := quittingTerminalSemanticExactPrefixOrbit_mem_carrier
      reward handoff.repairedSemanticSource
        handoff.repairedSemanticSource_mem_carrier time
    exact (quittingTerminalSemanticCarrier_mem_box reward _
      (abs_reward_le_quittingRewardBound reward) hpair).1
  anchor_floor := hfloor
  policy := by
    intro time
    rw [quittingTerminalSemanticExactPrefixOrbit_succ]
    rfl
  exactNash := fun time ↦
    quittingTerminalSemanticSelectedExactRoot_isZeroNash reward _

/-- The generic finite collision budget, instantiated on the actual repaired
stationary source and the selected exact root chronology. -/
theorem singletonGap_repairedExactPrefix_finiteCollisionBudget
    [Nontrivial ι]
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap)
    (hterminalGap : 0 < terminalGap) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexploit : HasTerminalExploitabilityGap reward terminalGap)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who)
    (hsingleton :
      quittingTerminalPayoff reward
          (quittingSingletonBaseRepairedProfile reward owner free point)
            handoff.outsideDebtor + terminalGap / 2 ≤
        reward (quittingSingletonTerminal handoff.outsideDebtor)
          handoff.outsideDebtor)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (hbudget : quittingTerminalSemanticDebtSum handoff.repairedSemanticSource -
        quittingTerminalSemanticDebtSum minimum <
      (horizon : ℝ) * quittingTerminalSemanticDebtSum minimum *
        ((terminalGap / 4) / (terminalGap / 4 + 2 * M) *
          ((terminalGap / 4) *
            (terminalGap / (4 * M)) ^ (Fintype.card ι - 1)) /
              (8 * M))) :
    let path := handoff.repairedExactFinitePrefix hfloor horizon
    (∃ time, 1 ≤ time ∧ time ≤ path.horizon ∧
        reward (quittingSingletonTerminal handoff.outsideDebtor)
              handoff.outsideDebtor - terminalGap / 4 <
            path.value time handoff.outsideDebtor ∧
        terminalGap / 4 < path.value time handoff.outsideDebtor -
          path.value 0 handoff.outsideDebtor ∧
        (terminalGap / 4) / (terminalGap / 4 + 2 * M) ≤
          quittingRootAbsorptionMass (path.roots 0)) ∨
      ∃ time, time < path.horizon ∧ ∃ crossedOwner,
        IsQuittingSingletonGapCrossedOwner (path.roots time)
          handoff.outsideDebtor crossedOwner
            ((terminalGap / 4) / (terminalGap / 4 + 2 * M))
            (terminalGap / (4 * M)) ∧
        (terminalGap / 4) / (terminalGap / 4 + 2 * M) ≤
          quittingRootAbsorptionMass (path.roots time) := by
  dsimp only
  apply QuittingPunishmentFloorFinitePrefix.singletonGap_finiteCollisionBudget
    (handoff.repairedExactFinitePrefix hfloor horizon)
    handoff.repairedSemanticSource minimum handoff.outsideDebtor
    hterminalGap hM (by positivity) hreward hexploit
    handoff.repairedSemanticSource_mem_carrier rfl hminimumCarrier hminimum
    hminimumPositive
  · change quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point)
          handoff.outsideDebtor ≤
      reward (quittingSingletonTerminal handoff.outsideDebtor)
          handoff.outsideDebtor - 2 * (terminalGap / 4)
    linarith
  · change 0 < horizon
    exact hhorizon
  · change quittingTerminalSemanticDebtSum handoff.repairedSemanticSource -
        quittingTerminalSemanticDebtSum minimum <
      (horizon : ℝ) * quittingTerminalSemanticDebtSum minimum *
        ((terminalGap / 4) / (terminalGap / 4 + 2 * M) *
          ((terminalGap / 4) *
            (terminalGap / (4 * M)) ^ (Fintype.card ι - 1)) /
              (8 * M))
    exact hbudget

/-- Charged payoff recurrence on segments of the actual selected exact orbit
is consumed by the single-seam projective compiler.  Only payoff coordinates
recur; no root recurrence is required. -/
theorem exists_uniformPayoff_of_repairedExactOrbit_chargedPayoffRecurrence
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who)
    (chargeThreshold : ℝ) (hcharge : 0 < chargeThreshold)
    (hrecurrence : ∀ endpointError : ℝ, 0 < endpointError →
      ∃ start horizon : ℕ, 0 < horizon ∧
        (∀ who,
          |(handoff.repairedExactInfiniteOrbit hfloor).value start who -
            (handoff.repairedExactInfiniteOrbit hfloor).value
              (start + horizon) who| ≤ endpointError) ∧
        chargeThreshold ≤ quittingRootAbsorptionMass
          ((handoff.repairedExactInfiniteOrbit hfloor).roots start)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  letI : Nonempty ι := ⟨handoff.outsideDebtor⟩
  apply quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
    reward
  intro error herror
  have hendpoint : 0 < error * chargeThreshold := mul_pos herror hcharge
  obtain ⟨start, horizon, hhorizon, hclose, hstage⟩ :=
    hrecurrence (error * chargeThreshold) hendpoint
  let orbit := handoff.repairedExactInfiniteOrbit hfloor
  let segment := orbit.toFiniteSegment start horizon
  apply exists_singleSeamProjectiveLasso_of_floorPrefix_payoffNearReturn
    segment chargeThreshold (error * chargeThreshold) error hcharge
      hendpoint.le le_rfl
  · intro who
    change |orbit.value start who - orbit.value (start + horizon) who| ≤
      error * chargeThreshold
    exact hclose who
  · refine ⟨0, ?_, ?_⟩
    · change 0 < horizon
      exact hhorizon
    · change chargeThreshold ≤
        quittingRootAbsorptionMass (orbit.roots start)
      exact hstage

end QuittingSingletonBaseStationaryHandoff

namespace QuittingTerminalExploitabilityWitness

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {owner : ι} {free : Finset ι}
variable {point : mixedPolytope (quittingBinaryForm free).sig}
variable {delta : ℝ}

/-- In a game carrying the terminal exploitability witness, every fixed
positive charge disappears along the actual selected exact orbit.  Hence the
charged recurrence premise above cannot hold at any positive threshold. -/
theorem repairedExactOrbit_absorption_tendsto_zero
    (witness : QuittingTerminalExploitabilityWitness reward)
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta witness.terminalGap)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who) :
    Tendsto (fun time ↦ quittingRootAbsorptionMass
        ((handoff.repairedExactInfiniteOrbit hfloor).roots time))
      atTop (nhds 0) :=
  witness.infiniteOrbit_absorptionMass_tendsto_zero
    (handoff.repairedExactInfiniteOrbit hfloor)

/-- Every positive absorption threshold is crossed only finitely far along
the actual selected exact orbit. -/
theorem repairedExactOrbit_eventually_absorption_lt
    (witness : QuittingTerminalExploitabilityWitness reward)
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta witness.terminalGap)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who)
    (chargeThreshold : ℝ) (hcharge : 0 < chargeThreshold) :
    ∀ᶠ time in atTop, quittingRootAbsorptionMass
        ((handoff.repairedExactInfiniteOrbit hfloor).roots time) <
      chargeThreshold :=
  (witness.repairedExactOrbit_absorption_tendsto_zero handoff hfloor)
    |>.eventually_lt_const hcharge

/-- The maintained charged payoff-recurrence premise is impossible for the
actual selected endpoint stack under the terminal exploitability witness. -/
theorem not_repairedExactOrbit_chargedPayoffRecurrence
    (witness : QuittingTerminalExploitabilityWitness reward)
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta witness.terminalGap)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward
        (quittingSingletonBaseRepairedProfile reward owner free point) who)
    (chargeThreshold : ℝ) (hcharge : 0 < chargeThreshold) :
    ¬ (∀ endpointError : ℝ, 0 < endpointError →
      ∃ start horizon : ℕ, 0 < horizon ∧
        (∀ who,
          |(handoff.repairedExactInfiniteOrbit hfloor).value start who -
            (handoff.repairedExactInfiniteOrbit hfloor).value
              (start + horizon) who| ≤ endpointError) ∧
        chargeThreshold ≤ quittingRootAbsorptionMass
          ((handoff.repairedExactInfiniteOrbit hfloor).roots start)) := by
  intro hrecurrence
  exact witness.not_exists_uniformEquilibriumPayoff
    (handoff.exists_uniformPayoff_of_repairedExactOrbit_chargedPayoffRecurrence
      hfloor chargeThreshold hcharge hrecurrence)

end QuittingTerminalExploitabilityWitness

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {seed : Finset ι}

/-- **Actual large-base source-to-stack adapter.**  The endpoint atom and the
floor dispatch refer to the same repaired stationary source.  In the
floor-safe arm the output is a literal infinite exact orbit whose initial
payoff is exactly that source payoff; the other arm retains the named free
player witnessing floor failure. -/
theorem LargeBasePaidStationaryHandoff.endpointAtom_floorFailure_or_exactOrbit
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (handoff : cycle.LargeBasePaidStationaryHandoff)
    (bound : ℝ) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ semantic : QuittingSingletonBaseStationaryHandoff reward
        handoff.owner {handoff.paid, handoff.first, handoff.second}
          handoff.point handoff.delta witness.terminalGap,
      Nonempty (QuittingPaidEndpointAtom reward
        (quittingSingletonBaseRepairedProfile reward handoff.owner
          {handoff.paid, handoff.first, handoff.second} handoff.point)
        semantic.outsideDebtor witness.terminalGap bound) ∧
      ((∃ who ∈ ({handoff.paid, handoff.first, handoff.second} : Finset ι),
          quittingTerminalPayoff reward
              (quittingSingletonBaseRepairedProfile reward handoff.owner
                {handoff.paid, handoff.first, handoff.second} handoff.point) who <
            quittingPunishmentValue reward who) ∨
        ∃ orbit : QuittingPunishmentFloorInfiniteOrbit reward,
          orbit.value 0 = quittingTerminalPayoff reward
            (quittingSingletonBaseRepairedProfile reward handoff.owner
              {handoff.paid, handoff.first, handoff.second} handoff.point)) := by
  obtain ⟨semantic, hatom⟩ := handoff.paidEndpointAtom bound hbound hreward
  refine ⟨semantic, hatom, ?_⟩
  rcases semantic.floor_dispatch with hfloor | hfloor
  · right
    refine ⟨semantic.repairedExactInfiniteOrbit hfloor, ?_⟩
    rfl
  · exact Or.inl hfloor

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

end GameTheory
