/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Debt.Quantitative
import UniformEquilibrium.Quitting.Debt.Dynamic.ChargeTimeCompactEdge
import UniformEquilibrium.Quitting.Debt.Dynamic.StatePreservingChronologyCapacity

/-!
# Counterexample adapters for state-preserving chronology capacity

The production owner defines the exact-D chronology capacity and its generic
near-maximality and charge-time interfaces. The terminal exploitability witness bounds
that capacity and gives every member chain aggregate debt at least its terminal
gap.

Consequently, for every positive tolerance there is one finite chronology which
simultaneously carries positive calibrated debt and admits no exact bounded
predecessor with absorption as large as the tolerance.  Compactness is not used
to assert attainment of the infinite-horizon supremum.  The result is the exact
finite near-maximality statement needed before any projective extraction.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {cutoff : ℕ}

/-- The terminal gap is retained by every admissible zero-boundary chain,
not only by the selected minimizer. -/
theorem terminalGap_le_zeroBoundaryChainAggregateDebt
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    witness.terminalGap ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path := by
  letI : Nonempty ι := witness.nonempty_players
  exact (witness.terminalGap_le_finiteMinMaxDynamicDebt cutoff).trans
    ((quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le
        reward cutoff path hpath).trans
      (quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
        reward cutoff path hpath))

/-- **State-preserving near-maximal chronology.**  One finite exact-D chain
simultaneously carries aggregate initial debt at least the regime gap and has
less than `ε` absorption available at every exact bounded prepend. -/
theorem exists_nearMaximal_positiveDebt_zeroBoundaryChronology
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
      path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
      witness.terminalGap ≤
        quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path ∧
      quittingZeroBoundaryChronologyCapacity reward - ε <
        quittingFiniteZeroBoundaryChainCharge cutoff path ∧
      ∀ predecessor : QuittingNashBellmanPoint ι,
        predecessor ∈ quittingNashBellmanBox (quittingRewardBound reward) →
        IsQuittingNashBellmanEdge reward predecessor (path 0) →
        quittingRootAbsorptionMass
          (quittingRootOfSimplex predecessor.2) < ε := by
  have hbounded : BddAbove (quittingZeroBoundaryChronologyCharges reward) :=
    quittingZeroBoundaryChronologyCharges_bddAbove
      hpunishment witness.prefixCharge_le
  obtain ⟨cutoff, path, hpath, hnear, hprepend⟩ :=
    exists_nearMaximal_zeroBoundaryChronology hbounded hε
  exact ⟨cutoff, path, hpath,
    terminalGap_le_zeroBoundaryChainAggregateDebt witness cutoff path hpath,
    hnear, hprepend⟩

/-- The compact Nash--Bellman predecessor correspondence turns the universal
small-prepend conclusion into one actual state-matched edge.  Its successor
is the positive-debt initial point of the same near-maximal chronology. -/
theorem exists_nearMaximal_positiveDebtChronology_smallPredecessor
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
      ∃ predecessor : QuittingNashBellmanPoint ι,
        path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
        witness.terminalGap ≤
          quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff path ∧
        predecessor ∈ quittingNashBellmanBox (quittingRewardBound reward) ∧
        IsQuittingNashBellmanEdge reward predecessor (path 0) ∧
        quittingRootAbsorptionMass
          (quittingRootOfSimplex predecessor.2) < ε := by
  obtain ⟨cutoff, path, hpath, hdebt, _hnear, hsmall⟩ :=
    exists_nearMaximal_positiveDebt_zeroBoundaryChronology
      witness hpunishment hε
  obtain ⟨predecessor, hpredecessor, hedge⟩ :=
    exists_quittingNashBellmanPredecessor reward
      (abs_reward_le_quittingRewardBound reward) (path 0) (hpath.1 0)
  exact ⟨cutoff, path, predecessor, hpath, hdebt, hpredecessor, hedge,
    hsmall predecessor hpredecessor hedge⟩

/-- **Projective one-edge readout of chronology near-maximality.**  At every
scale there is a genuine state-matched exact dynamic-debt edge whose successor
retains aggregate debt at least the terminal gap and whose absorption is below
that scale.  Either the edge is already on the zero-absorption face, or its
normalized value drift is uniformly bounded coordinatewise. -/
theorem exists_nearMaximal_positiveDebt_smallDynamicDebtEdge
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ current successor : QuittingDebtPoint ι,
      current ∈ quittingDebtBox reward ∧
      successor ∈ quittingDebtBox reward ∧
      IsQuittingDynamicDebtEdge reward current successor ∧
      witness.terminalGap ≤ ∑ who, successor.2 who ∧
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) < ε ∧
      (quittingRootAbsorptionMass
            (quittingRootOfSimplex current.1.2) = 0 ∨
        (0 < quittingRootAbsorptionMass
              (quittingRootOfSimplex current.1.2) ∧
          ∀ who,
            |(successor.1.1 who - current.1.1 who) /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2)| ≤
              2 * quittingRewardBound reward)) := by
  obtain ⟨cutoff, path, predecessor, hpath, hdebt, hpredecessor, hedge,
      hsmall⟩ :=
    exists_nearMaximal_positiveDebtChronology_smallPredecessor
      witness hpunishment hε
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) :=
    quittingFiniteNashBellmanPathPrependPoint_mem reward cutoff path hpath
      predecessor hpredecessor hedge
  let current := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (cutoff + 1) extended 0
  let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward (cutoff + 1) extended 1
  have hcurrent : current ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (cutoff + 1) extended hextended 0
  have hsuccessor : successor ∈ quittingDebtBox reward :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward (cutoff + 1) extended hextended 1
  have hdynamic : IsQuittingDynamicDebtEdge reward current successor :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_edge
      reward (cutoff + 1) extended hextended 0 (by omega)
  have hsuccessorDebt :
      witness.terminalGap ≤ ∑ who, successor.2 who := by
    calc
      witness.terminalGap ≤
          quittingFiniteNashBellmanPathAggregateDynamicDebt
            reward cutoff path := hdebt
      _ = ∑ who, successor.2 who := by
        unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
        apply Finset.sum_congr rfl
        intro who _
        change quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path who 0 =
          quittingFiniteNashBellmanPathDynamicDebt
            reward (cutoff + 1) extended who 1
        exact (quittingFiniteNashBellmanPathDynamicDebt_prependPoint_tail_eq
          reward cutoff predecessor path who).symm
  have hcurrentRoot : quittingRootOfSimplex current.1.2 =
      quittingRootOfSimplex predecessor.2 := by
    unfold current quittingFiniteNashBellmanPathDynamicDebtPoint
    rw [dif_pos (by omega)]
    rfl
  have hsmallCurrent : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) < ε := by
    rw [hcurrentRoot]
    exact hsmall
  refine ⟨current, successor, hcurrent, hsuccessor, hdynamic,
    hsuccessorDebt, hsmallCurrent, ?_⟩
  by_cases hzero : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) = 0
  · exact Or.inl hzero
  · have hactive : 0 < quittingRootAbsorptionMass
        (quittingRootOfSimplex current.1.2) :=
      lt_of_le_of_ne (by
        unfold quittingRootAbsorptionMass
        exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _))
        (Ne.symm hzero)
    exact Or.inr ⟨hactive, fun who ↦
      abs_normalized_valueDrift_le_two_rewardBound_of_dynamicDebtEdge
        current successor hsuccessor hdynamic hactive who⟩

/-- **Charge-time compact edge readout.**  The same state-matched edge has
uniformly bounded normalized payoff drift, debt loss, and marginal Quit
hazards whenever its absorption is positive.  These are exactly the bounded
coordinates available to a charge-time compactness argument. -/
theorem exists_nearMaximal_positiveDebt_chargeTimeCompactEdge
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ current successor : QuittingDebtPoint ι,
      current ∈ quittingDebtBox reward ∧
      successor ∈ quittingDebtBox reward ∧
      IsQuittingDynamicDebtEdge reward current successor ∧
      witness.terminalGap ≤ ∑ who, successor.2 who ∧
      quittingRootAbsorptionMass
          (quittingRootOfSimplex current.1.2) < ε ∧
      (quittingRootAbsorptionMass
            (quittingRootOfSimplex current.1.2) = 0 ∨
        (0 < quittingRootAbsorptionMass
              (quittingRootOfSimplex current.1.2) ∧
          (∀ who,
            |(successor.1.1 who - current.1.1 who) /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2)| ≤
              2 * quittingRewardBound reward) ∧
          (∀ who,
            quittingDynamicDebtCoordinateLoss current successor who /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2) ∈
              Set.Icc 0 (quittingPositiveSingletonDebtCap reward who)) ∧
          (∀ who,
            ((quittingRootOfSimplex current.1.2) who true).toReal /
                quittingRootAbsorptionMass
                  (quittingRootOfSimplex current.1.2) ∈
              Set.Icc (0 : ℝ) 1))) := by
  obtain ⟨current, successor, hcurrent, hsuccessor, hedge, hdebt,
      hsmall, hactiveOrZero⟩ :=
    exists_nearMaximal_positiveDebt_smallDynamicDebtEdge
      witness hpunishment hε
  refine ⟨current, successor, hcurrent, hsuccessor, hedge, hdebt,
    hsmall, ?_⟩
  rcases hactiveOrZero with hzero | ⟨hactive, hvalue⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨hactive, hvalue, ?_, ?_⟩
    · exact fun who ↦ normalized_dynamicDebtCoordinateLoss_mem_Icc
        current successor hcurrent hsuccessor hedge hactive who
    · exact fun who ↦ normalized_quitProbability_mem_Icc
        (quittingRootOfSimplex current.1.2) hactive who

end GameTheory
