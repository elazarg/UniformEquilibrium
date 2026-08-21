/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.R0Margin
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Circulation.DirectionBarycenter
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling

/-!
# Compactifying stationary approximate equilibria

A vanishing family of stationary approximate equilibria has three possible
compactification regimes.  Positive limiting absorption gives an exact
stationary fixed point.  At vanishing absorption, a tangential family whose
equilibrium error is little-o of total hazard gives a homogeneous singleton
LCP solution.  The remaining radial family stays quantitatively close to the
all-Continue apex.

This file supplies the quantitative tangent estimate and the compactness
interface.  It makes no claim that stationary approximate equilibria exist.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open Math.LinearProgramming Math.ProbabilityMassFunction Math.Topology
open QuittingLCPClassification

variable {iota : Type} [Fintype iota] [DecidableEq iota] [Nonempty iota]

omit [Nonempty iota] in
/-- Opponent absorption is bounded by the total stationary hazard. -/
theorem quittingRootOpponentAbsorptionMass_le_stationaryTotalHazard
    (root : iota → PMF Bool) (who : iota) :
    quittingRootOpponentAbsorptionMass root who ≤
      quittingStationaryTotalHazard root := by
  let deleted := Function.update root who (PMF.pure false)
  have hmass : quittingRootOpponentAbsorptionMass root who =
      quittingRootAbsorptionMass deleted := rfl
  rw [hmass]
  refine (quittingRootAbsorptionMass_le_stationaryTotalHazard deleted).trans ?_
  unfold quittingStationaryTotalHazard
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
  have hdeleted :
      ∑ owner ∈ Finset.univ.erase who, (deleted owner true).toReal =
        ∑ owner ∈ Finset.univ.erase who, (root owner true).toReal := by
    apply Finset.sum_congr rfl
    intro owner howner
    simp [deleted, Function.update_of_ne (Finset.mem_erase.mp howner).1]
  rw [hdeleted]
  simp only [deleted, Function.update_self, PMF.pure_apply,
    Bool.true_eq_false, reduceIte, ENNReal.toReal_zero, add_zero]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ ↦ ENNReal.toReal_nonneg)

omit [Nonempty iota] in
/-- On the normalized hazard simplex, the singleton LCP residual is the
singleton-reward barycenter minus the player's own singleton payoff. -/
theorem singletonLCPResidual_normalizedSoloMatrix_hazardDirection
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (root : iota → PMF Bool)
    (hpositive : 0 < quittingStationaryTotalHazard root) (who : iota) :
    singletonLCPResidual (normalizedSoloMatrix reward)
        (quittingStationaryHazardDirection root hpositive) who =
      quittingStationarySingletonDirectionBarycenter reward root who -
        quittingSoloReward reward who who := by
  classical
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold singletonLCPResidual wsum dotProduct quittingProjectiveLCPMatrix
    quittingStationarySingletonDirectionBarycenter
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hmass :
      ∑ owner, quittingStationaryHazardDirection root hpositive owner = 1 :=
    (quittingStationaryHazardDirection root hpositive).property.2
  rw [← Finset.sum_mul, hmass, one_mul]
  congr 1

/-- At small total hazard, the stationary endpoint difference is within
`10 M H` of the negative normalized singleton-LCP residual. -/
theorem abs_quittingRootEndpointDifference_add_singletonLCPResidual_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    {M : ℝ} (hreward : ∀ S who, |reward S who| ≤ M)
    (root : iota → PMF Bool) (who : iota)
    (hpositive : 0 < quittingStationaryTotalHazard root)
    (hhalf : quittingStationaryTotalHazard root ≤ 1 / 2) :
    |quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who +
        singletonLCPResidual (normalizedSoloMatrix reward)
          (quittingStationaryHazardDirection root hpositive) who| ≤
      10 * M * quittingStationaryTotalHazard root := by
  let H := quittingStationaryTotalHazard root
  let value := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  let solo := quittingSoloReward reward who who
  let mixture := quittingStationarySingletonDirectionBarycenter reward root who
  let opponentMass := quittingRootOpponentAbsorptionMass root who
  let quitValue := quittingStationaryFixedOpponentsQuitValue reward root who
  let continueReward := quittingStationaryFixedOpponentsContinueReward reward root who
  let continueMass := quittingStationaryFixedOpponentsContinueMass root who
  have hM : 0 ≤ M := by
    let player : iota := Classical.arbitrary iota
    exact (abs_nonneg (reward ⟨{player}, Finset.singleton_nonempty player⟩ player)).trans
      (hreward ⟨{player}, Finset.singleton_nonempty player⟩ player)
  have hopponent0 : 0 ≤ opponentMass := quittingRootAbsorptionMass_nonneg _
  have hopponent : opponentMass ≤ H :=
    quittingRootOpponentAbsorptionMass_le_stationaryTotalHazard root who
  have hvalue : |value| ≤ M :=
    abs_quittingTerminalPayoff_le reward _ who (fun S player ↦ hreward S player)
  have hquit : |quitValue - solo| ≤ 2 * M * opponentMass := by
    change |quittingStationaryFixedOpponentsQuitValue reward root who -
        reward (quittingSingletonTerminal who) who| ≤
      2 * M * quittingRootOpponentAbsorptionMass root who
    simpa using
      (abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
        (reward := reward) root who hreward)
  have hcontinue : |continueReward| ≤ M * opponentMass := by
    change |quittingFixedOpponentsContinueReward reward (fun _ ↦ root) who 0| ≤
      M * (1 - quittingFixedOpponentsContinueMass (fun _ ↦ root) who 0)
    simpa using
      (abs_quittingFixedOpponentsContinueReward_le_hazard
        reward (fun _ ↦ root) who 0 M hM (fun S ↦ hreward S who))
  have hcontinueMass : 1 - continueMass = opponentMass := rfl
  have hcontinueValue :
      |continueReward + continueMass * value - value| ≤
        2 * M * opponentMass := by
    have hsplit : continueReward + continueMass * value - value =
        continueReward - (1 - continueMass) * value := by ring
    rw [hsplit, hcontinueMass]
    calc
      |continueReward - opponentMass * value| ≤
          |continueReward| + |opponentMass * value| := abs_sub _ _
      _ ≤ M * opponentMass + opponentMass * M := by
        apply add_le_add hcontinue
        rw [abs_mul, abs_of_nonneg hopponent0]
        exact mul_le_mul_of_nonneg_left hvalue hopponent0
      _ = 2 * M * opponentMass := by ring
  have hendpoint : quittingRootEndpointDifference reward
        (fun player ↦ quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player)
        root who = quitValue - (continueReward + continueMass * value) := by
    simpa [quitValue, continueReward, continueMass, value] using
      quittingRootEndpointDifference_stationary_eq reward root who
  have hlocal :
      |quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who - (solo - value)| ≤ 4 * M * H := by
    rw [hendpoint]
    have hsplit :
        quitValue - (continueReward + continueMass * value) - (solo - value) =
          (quitValue - solo) - (continueReward + continueMass * value - value) := by
      ring
    rw [hsplit]
    calc
      |(quitValue - solo) -
          (continueReward + continueMass * value - value)| ≤
          |quitValue - solo| +
            |continueReward + continueMass * value - value| := abs_sub _ _
      _ ≤ 2 * M * opponentMass + 2 * M * opponentMass :=
        add_le_add hquit hcontinueValue
      _ ≤ 4 * M * H := by nlinarith
  have hbary : |value - mixture| ≤ 6 * M * H := by
    simpa [value, mixture, H] using
      (abs_stationaryPayoff_sub_singletonDirectionBarycenter_le
        reward hreward root who hpositive hhalf)
  rw [singletonLCPResidual_normalizedSoloMatrix_hazardDirection
    reward root hpositive who]
  have hsum :
      quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who + (mixture - solo) =
        (quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who - (solo - value)) + (mixture - value) := by ring
  rw [hsum]
  calc
    |_ + (mixture - value)| ≤ |_| + |mixture - value| := abs_add_le _ _
    _ ≤ 4 * M * H + 6 * M * H := by
      exact add_le_add hlocal (by simpa [abs_sub_comm] using hbary)
    _ = 10 * M * quittingStationaryTotalHazard root := by
      dsimp only [H]
      ring

end GameTheory
