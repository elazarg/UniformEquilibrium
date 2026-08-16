/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixChargedBridge
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Boundary.Holonomy.QuantitativeAggregateTerminalAnchor
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCapCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCalibration
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtConservation

/-!
# Aggregate-prefix consumption identities

For an aggregate-calibrated exact-`D` prefix, the immediate Never tail reads
the maximum dynamic debt exactly.  A genuinely prepended Nash--Bellman edge
obeys a complementary conservation estimate: residual aggregate debt is
bounded by transported old debt plus a charge-scaled seam.  These identities
make no counterexample or terminal-gap assumption.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingAggregateCalibratedTerminalAnchor

/-! ## The immediate Never cap -/

/-- Attaching Never immediately after the complete calibrated prefix reads
exactly the maximum playerwise dynamic debt.  This is the one elementary cap
whose boundary pair is already the zero-boundary pair used by exact-`D`.

A compressed Never cap with a positive internal cutoff does not satisfy this
identity: it retains the supplied behavioral word before reaching Never. -/
theorem immediateNever_terminalExploitability_eq_maxDynamicDebt
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward anchor.roots
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι))
          (anchor.last + 1)) =
      quittingFiniteNashBellmanPathMaxDynamicDebt
        reward (anchor.last + 1) anchor.path := by
  rw [← quittingPhaseSwitch_behavioralTailGain_eq_terminalExploitability
    reward anchor.roots
      (quittingElementaryCapRoots
        (.never : QuittingElementaryTailCap ι))
      (anchor.last + 1) (by omega)]
  simpa [QuittingAggregateCalibratedTerminalAnchor.roots] using
    (fullPrefix_behavioralTailGain_elementaryNever_eq_maxDynamicDebt
      reward anchor.last anchor.path anchor.path_mem)

/-- For the immediate Never cap, any bound on the next optimized residual
debt can be added to the objective drop.  No predecessor-edge structure is
needed for this algebraic comparison. -/
theorem immediateNever_terminalExploitability_le_drop_add_endpointBound
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (endpointBound : ℝ)
    (hendpoint :
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) ≤
        endpointBound) :
    quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward anchor.roots
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι))
          (anchor.last + 1)) ≤
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 1) -
        quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) +
        endpointBound := by
  calc
    quittingTerminalExploitability reward
        (quittingPhaseSwitchProfile reward anchor.roots
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι))
          (anchor.last + 1)) =
      quittingFiniteNashBellmanPathMaxDynamicDebt
        reward (anchor.last + 1) anchor.path :=
      immediateNever_terminalExploitability_eq_maxDynamicDebt anchor
    _ ≤ quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 1) anchor.path :=
      quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
        reward (anchor.last + 1) anchor.path anchor.path_mem
    _ = quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward (anchor.last + 1) := by
      rw [anchor.path_eq_minimizer]
      rfl
    _ ≤ quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 1) -
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
          reward (anchor.last + 2) +
        endpointBound := by
      linarith

/-! ## What joint charge actually controls -/

omit [Nonempty ι] in
/-- Exact one-edge conservation for a genuinely prepended calibrated chain.
The residual aggregate debt is bounded by the joint-Continue transport of
the old aggregate debt plus a diagonal seam paid by joint absorption.

This is the sharp universal replacement for a false bound of residual debt
by absorption alone.  The first term uses joint Continue mass and cannot be
discarded merely because the edge is reachable. -/
theorem prependResidual_le_jointContinue_mul_anchorDebt_add_charge
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (htail : edge.tail.1.1 = anchor.path 0) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 2)
        (quittingFiniteNashBellmanPathPrependPoint
          (anchor.last + 1) edge.current.1.1 anchor.path) ≤
      quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 1) anchor.path +
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        edge.toBoxEdge.absorptionCharge := by
  have hedgeAnchor : IsQuittingNashBellmanEdge reward edge.current.1.1
      (anchor.path 0) := by
    rw [← htail]
    exact edge.exactEdge
  let extended := quittingFiniteNashBellmanPathPrependPoint
    (anchor.last + 1) edge.current.1.1 anchor.path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet
        reward (anchor.last + 2) := by
    simpa [extended, Nat.add_assoc] using
      (quittingFiniteNashBellmanPathPrependPoint_mem
        reward (anchor.last + 1) anchor.path anchor.path_mem
        edge.current.1.1 edge.current.1.2 hedgeAnchor)
  let current := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (anchor.last + 2) extended 0
  let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (anchor.last + 2) extended 1
  have hcurrentBox : current ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (anchor.last + 2) extended hextended 0
  have hsuccessorBox : successor ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (anchor.last + 2) extended hextended 1
  have hdebtEdge : IsQuittingDynamicDebtEdge reward current successor :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_edge
      reward (anchor.last + 2) extended hextended 0 (by omega)
  have hcurrentPoint : current.1 = edge.current.1.1 := by
    simp [current, quittingFiniteNashBellmanPathDynamicDebtPoint, extended]
  have hcurrentDebt (who : ι) : current.2 who =
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 2) extended who 0 := by
    simp [current, quittingFiniteNashBellmanPathDynamicDebtPoint]
  have hsuccessorDebt (who : ι) : successor.2 who =
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 1) anchor.path who 0 := by
    rw [show successor.2 who =
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 2) extended who 1 by
          simp [successor, quittingFiniteNashBellmanPathDynamicDebtPoint]]
    simpa [extended, Nat.add_assoc] using
      (quittingFiniteNashBellmanPathDynamicDebt_prependPoint_tail_eq
        reward (anchor.last + 1) edge.current.1.1 anchor.path who)
  have hconservation (who : ι) :
      current.2 who =
        quittingStationaryContinueMass
            (quittingRootOfSimplex edge.current.1.1.2) * successor.2 who +
          quittingDynamicDebtSeam current who := by
    have h := quittingDynamicDebt_eq_continueMass_mul_add_seam
      current successor hdebtEdge hsuccessorBox.2.1 who
    rwa [hcurrentPoint] at h
  have hseam (who : ι) :
      quittingDynamicDebtSeam current who ≤
        quittingRewardBound reward * edge.toBoxEdge.absorptionCharge := by
    have hraw := quittingDynamicDebtSeam_le_cap_mul_absorptionMass
      current hcurrentBox who
    have hcap : quittingPositiveSingletonDebtCap reward who ≤
        quittingRewardBound reward :=
      (le_abs_self _).trans
        (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
    have hcharge0 : 0 ≤ edge.toBoxEdge.absorptionCharge :=
      edge.toBoxEdge.absorptionCharge_nonneg
    rw [hcurrentPoint] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_right hcap hcharge0)
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  rw [show (∑ who,
      quittingFiniteNashBellmanPathDynamicDebt
        reward (anchor.last + 2) extended who 0) =
      ∑ who, current.2 who by
        apply Finset.sum_congr rfl
        intro who _
        exact (hcurrentDebt who).symm]
  calc
    (∑ who, current.2 who) =
        ∑ who,
          (quittingStationaryContinueMass
              (quittingRootOfSimplex edge.current.1.1.2) * successor.2 who +
            quittingDynamicDebtSeam current who) := by
      apply Finset.sum_congr rfl
      intro who _
      exact hconservation who
    _ = quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
          (∑ who, successor.2 who) +
        ∑ who, quittingDynamicDebtSeam current who := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
          (∑ who, successor.2 who) +
        ∑ _who : ι,
          (quittingRewardBound reward * edge.toBoxEdge.absorptionCharge) := by
      have hs : (∑ who, quittingDynamicDebtSeam current who) ≤
          ∑ _who : ι,
            (quittingRewardBound reward *
              edge.toBoxEdge.absorptionCharge) := by
        apply Finset.sum_le_sum
        intro who _
        exact hseam who
      exact add_le_add_right hs _
    _ = quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
          (∑ who,
            quittingFiniteNashBellmanPathDynamicDebt
              reward (anchor.last + 1) anchor.path who 0) +
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          edge.toBoxEdge.absorptionCharge := by
      rw [show (∑ who, successor.2 who) =
          ∑ who, quittingFiniteNashBellmanPathDynamicDebt
            reward (anchor.last + 1) anchor.path who 0 by
        apply Finset.sum_congr rfl
        intro who _
        exact hsuccessorDebt who]
      simp [mul_assoc]

omit [Nonempty ι] in
/-- The exact extra observable needed to turn conservation into a pure charge
bound is the joint-Continue-carried old debt.  If that surviving potential is
itself charged at scale `carriedScale`, the whole prepended residual is
charged at scale `carriedScale + card * rewardBound`. -/
theorem prependResidual_le_charge_of_carriedDebt_le_charge
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (edge : QuittingPunishmentFloorReachableEdge reward)
    (htail : edge.tail.1.1 = anchor.path 0)
    (carriedScale : ℝ)
    (hcarried :
      quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 1) anchor.path ≤
        carriedScale * edge.toBoxEdge.absorptionCharge) :
    quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 2)
        (quittingFiniteNashBellmanPathPrependPoint
          (anchor.last + 1) edge.current.1.1 anchor.path) ≤
      (carriedScale +
          (Fintype.card ι : ℝ) * quittingRewardBound reward) *
        edge.toBoxEdge.absorptionCharge := by
  have hconservation :=
    prependResidual_le_jointContinue_mul_anchorDebt_add_charge
      anchor edge htail
  calc
    quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward (anchor.last + 2)
        (quittingFiniteNashBellmanPathPrependPoint
          (anchor.last + 1) edge.current.1.1 anchor.path) ≤
      quittingStationaryContinueMass
          (quittingRootOfSimplex edge.current.1.1.2) *
        quittingFiniteNashBellmanPathAggregateDynamicDebt
          reward (anchor.last + 1) anchor.path +
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        edge.toBoxEdge.absorptionCharge := hconservation
    _ ≤ carriedScale * edge.toBoxEdge.absorptionCharge +
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          edge.toBoxEdge.absorptionCharge := add_le_add_left hcarried _
    _ = (carriedScale +
          (Fintype.card ι : ℝ) * quittingRewardBound reward) *
        edge.toBoxEdge.absorptionCharge := by ring

end QuittingAggregateCalibratedTerminalAnchor

end GameTheory
