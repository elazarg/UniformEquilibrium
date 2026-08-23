/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Debt.Source.DynamicAlternative
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilitySmallPlayers
import UniformEquilibrium.Quitting.Boundary.Analytic.ChargeTangent.SupportLiftFarkas
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair
import UniformEquilibrium.Quitting.Boundary.Repair.TerminalFunding.IncomingPath
import UniformEquilibrium.Quitting.Debt.Dynamic.ReachableCarryTelescope

/-!
# A frozen-root alternative for funding the terminal singleton cap

The terminal point of a finite zero-boundary Nash--Bellman chain has payoff
zero, but its stored product root is unconstrained.  This file observes that
the global floor-admissible path potential depends only on the payoff
coordinate: the first edge of any nonempty path may be re-rooted at another
state with the same payoff.  Consequently an incoming edge to *any* boxed
zero-payoff root reserves capacity at the selected terminal point.

For a supplied product root, the frozen-root affine alternative therefore
gives either a literal incoming exact edge which funds the terminal cap, or
an explicit finite Farkas certificate for that root.  The result does not
assert that the certificate rules out every product root.  In particular,
the strict-interior support decoder does not cover the pure-Quit boundary.
-/

noncomputable section

namespace GameTheory

open Finset
open Math.ChargedPathBudget
open Math.LinearProgramming.FlowCostateDuality
open Math.ProbabilityMassFunction
open QuittingFiniteDynamicDebtAdmissibleChronology
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingFiniteDynamicDebtAdmissibleChronology

variable {cutoff : ℕ}
variable (path : QuittingFiniteNashBellmanPath ι cutoff)
variable (hpath : path ∈
  quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
variable (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)

/-- A physical frozen-root lift whose one-stage absorption charge pays the
terminal singleton debt proves the exact terminal boundary comparison.  The
edge lands at a zero-payoff state carrying the supplied root; potential
invariance transfers its reserved capacity to the selected terminal root. -/
theorem terminal_debt_le_aggregateCapacityAccount_of_frozenRootLift
    (witness : QuittingTerminalExploitabilityWitness reward)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root) :
    debt (reward := reward) path cutoff ≤
      aggregateCapacityAccount path hpath hpunishment cutoff := by
  let sourceState := quittingFrozenRootContinuationAdmissibleState
    (reward := reward) 0 root support continuation hlift
      quittingAllContinueSimplexRoot
  let zeroState := quittingZeroPayoffAdmissibleState
    (reward := reward) hpunishment root
  let edge : QuittingPunishmentFloorAdmissibleEdge reward :=
    { tail := sourceState
      current := zeroState
      exactEdge := isQuittingNashBellmanEdge_of_frozenRootContinuationLift
        0 (quittingPunishmentValue reward) (quittingRewardBound reward)
        root support continuation hlift hsupport quittingAllContinueSimplexRoot }
  have hpotential : quittingPunishmentFloorAdmissiblePotential reward zeroState =
      quittingPunishmentFloorAdmissiblePotential reward
        (quittingFiniteDynamicDebtAdmissibleState
          path hpath hpunishment cutoff) := by
    apply quittingPunishmentFloorAdmissiblePotential_eq_of_payoff_eq
    change (0 : Payoff ι) =
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path cutoff).1.1
    exact (terminal_payoff_eq_zero path hpath).symm
  have hdecrement :=
    quittingPunishmentFloorAdmissiblePotential_predecessor_decrement
      witness.prefixCharge_le edge
  have hsource :=
    admissiblePotential_le_prefixChargeBound witness.prefixCharge_le sourceState
  have hcharge : edge.toBoxEdge.absorptionCharge =
      quittingRootAbsorptionMass root := by
    change quittingRootAbsorptionMass
      (quittingRootOfSimplex (quittingFrozenRootLiftSimplex root)) =
        quittingRootAbsorptionMass root
    rw [quittingRootOfSimplex_frozenRootLiftSimplex]
  have hscale : 0 ≤ (Fintype.card ι : ℝ) * quittingRewardBound reward :=
    mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward)
  calc
    debt (reward := reward) path cutoff ≤
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          quittingRootAbsorptionMass root := hpays
    _ = (Fintype.card ι : ℝ) * quittingRewardBound reward *
          edge.toBoxEdge.absorptionCharge := by rw [hcharge]
    _ ≤ (Fintype.card ι : ℝ) * quittingRewardBound reward *
        remainingCapacity path hpath hpunishment cutoff := by
      apply mul_le_mul_of_nonneg_left _ hscale
      unfold remainingCapacity
      rw [← hpotential]
      linarith
    _ = aggregateCapacityAccount path hpath hpunishment cutoff := rfl

/-- The terminal comparison from a physical frozen-root lift closes the
entire intrinsic carry telescope. -/
theorem debt_zero_le_aggregateCapacityAccount_zero_of_frozenRootLift
    (witness : QuittingTerminalExploitabilityWitness reward)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root) :
    debt (reward := reward) path 0 ≤
      aggregateCapacityAccount path hpath hpunishment 0 := by
  apply debt_zero_le_aggregateCapacityAccount_zero_of_far
    path hpath hpunishment witness.prefixCharge_le
  exact terminal_debt_le_aggregateCapacityAccount_of_frozenRootLift
    path hpath hpunishment witness root support hsupport continuation hlift
      hpays

/-- A terminal capacity comparison propagates to every earlier point of the
same intrinsic finite chronology. -/
theorem debt_le_aggregateCapacityAccount_of_far_at
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hfar : debt (reward := reward) path cutoff ≤
      aggregateCapacityAccount path hpath hpunishment cutoff) :
    ∀ time, time ≤ cutoff →
      debt (reward := reward) path time ≤
        aggregateCapacityAccount path hpath hpunishment time := by
  intro time htime
  exact Nat.decreasingInduction (n := cutoff) (motive := fun time _ ↦
      debt (reward := reward) path time ≤
        aggregateCapacityAccount path hpath hpunishment time)
    (fun liveTime hlive ih ↦ by
      have hdebt := debt_step path hpath liveTime hlive
      have haccount := source_add_aggregateCapacityAccount_succ_le
        path hpath hpunishment witness.prefixCharge_le liveTime hlive
      have hsurvival : survival (reward := reward) path liveTime ≤ 1 :=
        quittingStationaryContinueMass_le_one _
      have haccountNext : 0 ≤
          aggregateCapacityAccount path hpath hpunishment (liveTime + 1) :=
        aggregateCapacityAccount_nonneg
          path hpath hpunishment witness.prefixCharge_le (liveTime + 1)
      calc
        debt (reward := reward) path liveTime =
            source (reward := reward) path liveTime +
              survival (reward := reward) path liveTime *
                debt (reward := reward) path (liveTime + 1) := hdebt
        _ ≤ source (reward := reward) path liveTime +
              survival (reward := reward) path liveTime *
                aggregateCapacityAccount path hpath hpunishment
                  (liveTime + 1) := by
            gcongr
            exact survival_nonneg path liveTime
        _ ≤ source (reward := reward) path liveTime +
              aggregateCapacityAccount path hpath hpunishment
                (liveTime + 1) := by
            gcongr
            exact mul_le_of_le_one_left haccountNext hsurvival
        _ ≤ aggregateCapacityAccount path hpath hpunishment liveTime :=
          haccount)
    hfar htime

/-- A physical frozen-root terminal lift dominates aggregate debt by the
capacity account at every point, not only at the initial point. -/
theorem debt_le_aggregateCapacityAccount_of_frozenRootLift_at
    (witness : QuittingTerminalExploitabilityWitness reward)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root) :
    ∀ time, time ≤ cutoff →
      debt (reward := reward) path time ≤
        aggregateCapacityAccount path hpath hpunishment time := by
  apply debt_le_aggregateCapacityAccount_of_far_at
    path hpath hpunishment witness
  exact terminal_debt_le_aggregateCapacityAccount_of_frozenRootLift
    path hpath hpunishment witness root support hsupport continuation hlift
      hpays

/-- **Tight initial capacity forces immediate zero-source entry.**  Once a
physical incoming lift has paid the positive terminal boundary, the carry
comparison holds at every date.  If the initial capacity account is no
larger than exact initial debt, the two are equal.  Exact debt recursion and
the stronger additive capacity recursion then force aggregate debt source
zero at date zero, or (when the next debt itself is zero) at date one.

This is the sharp extra comparison needed to turn boundary funding into a
literal exposed-face edge.  The landed minimizer APIs provide the opposite
inequality but do not currently prove this reverse inequality. -/
theorem source_zero_or_succ_zero_of_frozenRootLift_and_initial_tight
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcutoff : 0 < cutoff)
    (hterminal : 0 < debt (reward := reward) path cutoff)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root)
    (htight : aggregateCapacityAccount path hpath hpunishment 0 ≤
      debt (reward := reward) path 0) :
    source (reward := reward) path 0 = 0 ∨
      (1 < cutoff ∧ source (reward := reward) path 1 = 0) := by
  have hdom := debt_le_aggregateCapacityAccount_of_frozenRootLift_at
    path hpath hpunishment witness root support hsupport continuation hlift
      hpays
  have hdom0 := hdom 0 (Nat.zero_le cutoff)
  have heq0 : debt (reward := reward) path 0 =
      aggregateCapacityAccount path hpath hpunishment 0 :=
    le_antisymm hdom0 htight
  have hdom1 := hdom 1 hcutoff
  have hdebt0 := debt_step path hpath 0 hcutoff
  have haccount0 := source_add_aggregateCapacityAccount_succ_le
    path hpath hpunishment witness.prefixCharge_le 0 hcutoff
  have hcarry : aggregateCapacityAccount path hpath hpunishment 1 ≤
      survival (reward := reward) path 0 *
        debt (reward := reward) path 1 := by
    rw [← heq0] at haccount0
    norm_num at hdebt0 haccount0
    linarith
  have hkilled : debt (reward := reward) path 1 ≤
      survival (reward := reward) path 0 *
        debt (reward := reward) path 1 := hdom1.trans hcarry
  by_cases hnextDebt : debt (reward := reward) path 1 = 0
  · right
    have hcutoffOne : 1 < cutoff := by
      by_contra hnot
      have : cutoff = 1 := by omega
      subst cutoff
      linarith
    refine ⟨hcutoffOne, ?_⟩
    have hdebt1 := debt_step path hpath 1 hcutoffOne
    have hsource1 := source_nonneg path hpath 1
    have hcarry1 : 0 ≤ survival (reward := reward) path 1 *
        debt (reward := reward) path (1 + 1) :=
      mul_nonneg (survival_nonneg path 1) (debt_nonneg path hpath (1 + 1))
    rw [hnextDebt] at hdebt1
    linarith
  · left
    have hnextDebtPos : 0 < debt (reward := reward) path 1 :=
      lt_of_le_of_ne (debt_nonneg path hpath 1) (Ne.symm hnextDebt)
    have hsurvivalLe : survival (reward := reward) path 0 ≤ 1 :=
      quittingStationaryContinueMass_le_one _
    have hsurvivalEq : survival (reward := reward) path 0 = 1 := by
      nlinarith
    have hcharge : charge (reward := reward) path 0 = 0 := by
      unfold charge quittingRootAbsorptionMass
      change 1 - survival (reward := reward) path 0 = 0
      linarith
    have hsourceLe := source_le_card_mul_rewardBound_mul_charge
      path hpath 0
    rw [hcharge, mul_zero] at hsourceLe
    exact le_antisymm hsourceLe (source_nonneg path hpath 0)

include hpath hpunishment in
/-- Vanishing aggregate source puts the corresponding finite exact edge in
every playerwise debt-source exposed face.  A counterexample seam witness is
used only to certify that zero is the attained supporting value of the
compact carrier. -/
theorem all_debtSourceZeroFaces_of_source_eq_zero
    {witness : QuittingTerminalExploitabilityWitness reward}
    (seam : QuittingCounterexampleDynamicTailWitness witness)
    (time : ℕ) (htime : time < cutoff)
    (hsource : source (reward := reward) path time = 0) :
    ∀ selected,
      quittingDebtSourceObstructionFlow
          (quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path time,
            quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path (time + 1)) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) := by
  let edge : QuittingDebtPoint ι × QuittingDebtPoint ι :=
    (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time,
      quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path (time + 1))
  have hedge : edge ∈ quittingFloorDynamicDebtEdgeGraph reward := by
    constructor
    · exact ⟨quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
          reward cutoff path hpath time,
        quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
          reward cutoff path hpath (time + 1),
        quittingFiniteNashBellmanPathDynamicDebtPoint_edge
          reward cutoff path hpath time htime⟩
    · intro who
      exact ⟨quittingPunishmentValue_le_finiteDynamicDebtPoint_of_nonpos
          path hpath hpunishment time who,
        quittingPunishmentValue_le_finiteDynamicDebtPoint_of_nonpos
          path hpath hpunishment (time + 1) who⟩
  have hflow : quittingDebtSourceObstructionFlow edge ∈
      quittingDebtSourceOneStageObstructionCarrier reward :=
    ⟨edge, hedge, rfl⟩
  intro selected
  apply (seam.mem_exposedFace_quittingDebtSourceZeroFaceCostate_iff
    selected (quittingDebtSourceObstructionFlow edge)).2
  refine ⟨hflow, ?_⟩
  rw [quittingDebtSourceObstructionFlow_source]
  have hcoordinateNonneg : 0 ≤ quittingDynamicDebtSeam edge.1 selected :=
    quittingDynamicDebtSeam_nonneg edge.1 hedge.1.1 selected
  have hcoordinateLe : quittingDynamicDebtSeam edge.1 selected ≤
      source (reward := reward) path time := by
    unfold source
    exact Finset.single_le_sum
      (fun who _ ↦ quittingDynamicDebtSeam_nonneg edge.1 hedge.1.1 who)
      (Finset.mem_univ selected)
  rw [hsource] at hcoordinateLe
  exact le_antisymm hcoordinateLe hcoordinateNonneg

/-- Tight initial capacity upgrades a physical terminal lift to a literal
all-player zero-source exposed face at the first or second finite edge. -/
theorem all_debtSourceZeroFaces_zero_or_one_of_frozenRootLift_and_initial_tight
    {witness : QuittingTerminalExploitabilityWitness reward}
    (seam : QuittingCounterexampleDynamicTailWitness witness)
    (hcutoff : 0 < cutoff)
    (hterminal : 0 < debt (reward := reward) path cutoff)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root)
    (htight : aggregateCapacityAccount path hpath hpunishment 0 ≤
      debt (reward := reward) path 0) :
    (∀ selected,
      quittingDebtSourceObstructionFlow
          (quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path 0,
            quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path 1) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward)) ∨
      (1 < cutoff ∧ ∀ selected,
        quittingDebtSourceObstructionFlow
            (quittingFiniteNashBellmanPathDynamicDebtPoint
                reward cutoff path 1,
              quittingFiniteNashBellmanPathDynamicDebtPoint
                reward cutoff path 2) ∈
          exposedFace (quittingDebtSourceZeroFaceCostate selected)
            (quittingDebtSourceOneStageObstructionCarrier reward)) := by
  rcases source_zero_or_succ_zero_of_frozenRootLift_and_initial_tight
    path hpath hpunishment witness hcutoff hterminal root support hsupport
      continuation hlift hpays htight with hzero | ⟨hcutoff1, hzero⟩
  · exact Or.inl
      (all_debtSourceZeroFaces_of_source_eq_zero
        path hpath hpunishment seam 0 hcutoff hzero)
  · exact Or.inr ⟨hcutoff1,
      all_debtSourceZeroFaces_of_source_eq_zero
        path hpath hpunishment seam 1 hcutoff1 hzero⟩

/-- **Incoming frozen-root alternative.**  For any supplied interior-support
product root whose literal absorption would fund the terminal cap, either
the intrinsic carry gate closes by a genuine one-edge predecessor, or finite
Farkas multipliers certify infeasibility of the continuation system for that
specific root. -/
theorem debt_zero_le_aggregateCapacityAccount_zero_or_farkas_of_fundingRoot
    (witness : QuittingTerminalExploitabilityWitness reward)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (tailRoot : QuittingRootSimplex ι)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root) :
    (debt (reward := reward) path 0 ≤
      aggregateCapacityAccount path hpath hpunishment 0 ∧
        ∃ continuation,
          IsQuittingFrozenRootContinuationLift reward 0
            (quittingPunishmentValue reward) (quittingRewardBound reward)
            root support continuation ∧
          IsQuittingNashBellmanEdge reward
            (0, quittingFrozenRootLiftSimplex root)
            (continuation, tailRoot)) ∨
      ((¬ ∃ continuation,
        IsQuittingFrozenRootContinuationLift reward 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support continuation) ∧
        ∃ y : QuittingFrozenRootLiftEqRow ι support → ℝ,
          ∃ lambda : QuittingFrozenRootLiftIneqRow ι support → ℝ,
            IsQuittingFrozenRootLiftFarkasCertificate reward 0
              (quittingPunishmentValue reward) (quittingRewardBound reward)
              root support y lambda) := by
  rcases quittingFrozenRootNashBellmanEdge_or_farkas
      (reward := reward) 0 (quittingPunishmentValue reward)
      (quittingRewardBound reward) root support hsupport tailRoot with
    ⟨continuation, hlift, hedge⟩ | hfarkas
  · left
    exact ⟨debt_zero_le_aggregateCapacityAccount_zero_of_frozenRootLift
      path hpath hpunishment witness root support hsupport continuation hlift
        hpays, continuation, hlift, hedge⟩
  · exact Or.inr hfarkas

/-- **Strict terminal-cap alternative without a funding premise.**  If the
aggregate terminal debt is positive but strictly below the universal
`card * rewardBound` scale, a canonical single-owner hazard is chosen whose
one-stage absorption charge funds that debt exactly.  Either its frozen
continuation system produces the required incoming edge and closes the carry
gate, or the returned finite multipliers certify infeasibility for this
explicit funding root.

The saturated boundary where terminal debt equals the full scale is not
covered: it would force hazard one, outside the strict-interior support
decoder used by the affine alternative. -/
theorem strict_terminalDebt_fundingEdge_or_farkas
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tailRoot : QuittingRootSimplex ι)
    (hpositive : 0 < debt (reward := reward) path cutoff)
    (hstrict : debt (reward := reward) path cutoff <
      (Fintype.card ι : ℝ) * quittingRewardBound reward) :
    (debt (reward := reward) path 0 ≤
        aggregateCapacityAccount path hpath hpunishment 0 ∧
      ∃ root : ι → PMF Bool, ∃ support : Finset ι, ∃ continuation,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          debt (reward := reward) path cutoff ∧
        IsQuittingFrozenRootContinuationLift reward 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support continuation ∧
        IsQuittingNashBellmanEdge reward
          (0, quittingFrozenRootLiftSimplex root)
          (continuation, tailRoot)) ∨
      ∃ root : ι → PMF Bool, ∃ support : Finset ι,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          debt (reward := reward) path cutoff ∧
        HasQuittingFrozenRootLiftFarkasCertificate (reward := reward) 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support := by
  let scale := (Fintype.card ι : ℝ) * quittingRewardBound reward
  let terminalDebt := debt (reward := reward) path cutoff
  have hscale : 0 < scale := by
    dsimp [scale, terminalDebt] at hstrict ⊢
    linarith
  have hcard : 0 < Fintype.card ι := by
    by_contra hnot
    have hzero : Fintype.card ι = 0 := by omega
    simp [scale, hzero] at hscale
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  let owner : ι := Classical.choice inferInstance
  let p := terminalDebt / scale
  have hp0 : 0 < p := div_pos (by simpa [terminalDebt] using hpositive) hscale
  have hp1 : p < 1 := (div_lt_one hscale).2 (by
    simpa [terminalDebt, scale] using hstrict)
  let root := quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le
  let support : Finset ι := {owner}
  have hsupport : IsQuittingRootInteriorOnSupport root support := by
    exact isQuittingRootInteriorOnSupport_sureSetOwnerRoot_empty owner p hp0 hp1
  have habsorption : quittingRootAbsorptionMass root = p := by
    exact quittingRootAbsorptionMass_sureSetOwnerRoot_empty
      owner p hp0.le hp1.le
  have hfunds : scale * quittingRootAbsorptionMass root = terminalDebt := by
    rw [habsorption]
    dsimp [p]
    field_simp
  have hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root := by
    change terminalDebt ≤ scale * quittingRootAbsorptionMass root
    rw [hfunds]
  rcases debt_zero_le_aggregateCapacityAccount_zero_or_farkas_of_fundingRoot
      path hpath hpunishment witness root support hsupport tailRoot hpays with
    ⟨hcarry, continuation, hlift, hedge⟩ | hfarkas
  · left
    refine ⟨hcarry, root, support, continuation, hsupport, ?_, hlift, hedge⟩
    simpa [scale, terminalDebt] using hfunds
  · right
    refine ⟨root, support, hsupport, ?_, hfarkas⟩
    simpa [scale, terminalDebt] using hfunds

end QuittingFiniteDynamicDebtAdmissibleChronology

/-! ## Terminal exploitability witness exhaustion of the strict terminal branch -/

namespace QuittingAggregateCalibratedTerminalAnchor

/-- In a terminal exploitability witness the terminal aggregate debt is automatically
strictly below the `card * rewardBound` funding scale.  The important sharp
estimate is `terminal debt ≤ rewardBound`; the regime supplies at least four
players, so the saturated branch cannot occur. -/
theorem terminalAggregateDebt_lt_card_mul_rewardBound
    (witness : QuittingTerminalExploitabilityWitness reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    (∑ who, quittingPositiveSingletonDebtCap reward who) <
      (Fintype.card ι : ℝ) * quittingRewardBound reward := by
  have hdebtPos := anchor.terminalAggregateDebt_pos
  have hdebtLe : (∑ who, quittingPositiveSingletonDebtCap reward who) ≤
      quittingRewardBound reward :=
    sum_positiveSingletonDebtCap_le_quittingRewardBound
      (reward := reward)
  have hboundPos : 0 < quittingRewardBound reward :=
    hdebtPos.trans_le hdebtLe
  have hcard : (3 : ℝ) < Fintype.card ι := by
    exact_mod_cast witness.three_lt_card
  nlinarith

/-- **Terminal exploitability witness terminal-boundary alternative.**  For every
calibrated positive-debt anchor in the nonpositive-floor lane, the canonical
one-owner strict funding root is available automatically.  Hence the finite
boundary is genuinely exhausted by a floor-admissible incoming edge and the
carry comparison, unless explicit finite Farkas multipliers reject that
specific game-facing continuation system.

There is no saturated residual in a terminal exploitability witness: the sum-form
reward bound and `card ≥ 4` force strictness. -/
theorem boundaryCarry_fundingEdge_or_farkas
    (witness : QuittingTerminalExploitabilityWitness reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    (QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path 0 ≤
        QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment 0 ∧
      ∃ root : ι → PMF Bool, ∃ support : Finset ι, ∃ continuation,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) ∧
        IsQuittingFrozenRootContinuationLift reward 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support continuation ∧
        IsQuittingNashBellmanEdge reward
          (0, quittingFrozenRootLiftSimplex root)
          (continuation, quittingAllContinueSimplexRoot)) ∨
      ∃ root : ι → PMF Bool, ∃ support : Finset ι,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) ∧
        HasQuittingFrozenRootLiftFarkasCertificate (reward := reward) 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support := by
  apply QuittingFiniteDynamicDebtAdmissibleChronology.strict_terminalDebt_fundingEdge_or_farkas
    anchor.path anchor.path_mem hpunishment witness quittingAllContinueSimplexRoot
  · rw [QuittingFiniteDynamicDebtAdmissibleChronology.debt_cutoff_eq_sum_positiveSingletonDebtCap]
    exact anchor.terminalAggregateDebt_pos
  · rw [QuittingFiniteDynamicDebtAdmissibleChronology.debt_cutoff_eq_sum_positiveSingletonDebtCap]
    exact anchor.terminalAggregateDebt_lt_card_mul_rewardBound witness

/-- **Unconditional finite boundary-exhaustion trichotomy.**  In the
nonpositive-floor lane under a terminal exploitability witness, every calibrated anchor has
one of three game-facing outcomes:

* the first or second exact finite edge lies in every debt-source zero face;
* the initial admissible capacity account has strict positive slack over
  exact aggregate debt;
* explicit finite Farkas multipliers reject the canonical strictly mixed
  terminal-funding root.

Thus persistent positive debt source is priced by a literal, strictly
positive initial capacity slack.  Eliminating that slack requires the still
missing reverse objective comparison; terminal boundary domination alone
cannot do it. -/
theorem zeroFace_zero_or_one_or_initialCapacitySlack_or_farkas
    (witness : QuittingTerminalExploitabilityWitness reward)
    (seam : QuittingCounterexampleDynamicTailWitness witness)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    anchor.IsAllDebtSourceZeroFace 0 ∨
      (1 < anchor.last + 1 ∧ anchor.IsAllDebtSourceZeroFace 1) ∨
      QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path 0 <
        QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment 0 ∨
      ∃ root : ι → PMF Bool, ∃ support : Finset ι,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) ∧
        HasQuittingFrozenRootLiftFarkasCertificate (reward := reward) 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support := by
  rcases anchor.boundaryCarry_fundingEdge_or_farkas witness hpunishment with
    ⟨hcarry, root, support, continuation, hsupport, hfunds, hlift, _hedge⟩ |
      ⟨root, support, hsupport, hfunds, hfarkas⟩
  · by_cases htight :
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment 0 ≤
        QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path 0
    · have hterminal : 0 <
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) := by
        rw [debt_cutoff_eq_sum_positiveSingletonDebtCap]
        exact anchor.terminalAggregateDebt_pos
      have hpays :
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
              (reward := reward) anchor.path (anchor.last + 1) ≤
            (Fintype.card ι : ℝ) * quittingRewardBound reward *
              quittingRootAbsorptionMass root := by
        rw [hfunds]
      rcases
          all_debtSourceZeroFaces_zero_or_one_of_frozenRootLift_and_initial_tight
            anchor.path anchor.path_mem hpunishment seam (by omega) hterminal
              root support hsupport continuation hlift hpays htight with
            hzero | hnext
      · exact Or.inl (by
          simpa [IsAllDebtSourceZeroFace, debtSourceFlow] using hzero)
      · exact Or.inr (Or.inl ⟨hnext.1, by
          simpa [IsAllDebtSourceZeroFace, debtSourceFlow] using hnext.2⟩)
    · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge htight)))
  · exact Or.inr (Or.inr (Or.inr
      ⟨root, support, hsupport, hfunds, hfarkas⟩))

end QuittingAggregateCalibratedTerminalAnchor

end GameTheory
