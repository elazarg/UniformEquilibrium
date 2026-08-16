/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.ChargeTangent.SupportLiftFarkas
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair
import UniformEquilibrium.Quitting.Debt.Dynamic.DebtSourceObstructionCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.ReachableCarryTelescope

/-!
# Generic terminal-funding incoming-path infrastructure

The full floor-admissible path potential depends only on the payoff coordinate,
so an incoming edge to any boxed zero-payoff root reserves capacity at every
other zero-payoff root.  This module records the generic root, capacity, debt,
and saturation facts used by terminal-funding alternatives.  Counterexample
and attained-face consequences belong to diagnostic adapters.
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

private abbrev AdmissibleRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-! ## The admissible potential ignores the stored root -/

private theorem chargesFrom_subset_of_payoff_eq
    (first second : QuittingPunishmentFloorAdmissibleState reward)
    (hpayoff : first.1.1.1 = second.1.1.1) :
    (AdmissibleRelation reward).chargesFrom first ⊆
      (AdmissibleRelation reward).chargesFrom second := by
  rintro charge ⟨target, segment, rfl⟩
  cases segment with
  | nil state =>
      exact (AdmissibleRelation reward).zero_mem_chargesFrom second
  | cons edge rest =>
      let rerooted : QuittingPunishmentFloorAdmissibleEdge reward :=
        { tail := second
          current := edge.current
          exactEdge := by
            constructor
            · rw [← hpayoff]
              exact edge.exactEdge.1
            · rw [← hpayoff]
              exact edge.exactEdge.2 }
      refine ⟨_, .cons rerooted rest, ?_⟩
      simp [rerooted, AdmissibleRelation,
        quittingPunishmentFloorAdmissibleChargedRelation,
        QuittingPunishmentFloorAdmissibleEdge.toBoxEdge,
        QuittingPunishmentFloorBoxEdge.absorptionCharge,
        QuittingPunishmentFloorBoxEdge.root]

/-- The full floor-admissible path potential depends only on the payoff
coordinate, not on the product root stored alongside it.  The empty path is
replaced by an empty path and a nonempty path is re-rooted at its first edge. -/
theorem quittingPunishmentFloorAdmissiblePotential_eq_of_payoff_eq
    (first second : QuittingPunishmentFloorAdmissibleState reward)
    (hpayoff : first.1.1.1 = second.1.1.1) :
    quittingPunishmentFloorAdmissiblePotential reward first =
      quittingPunishmentFloorAdmissiblePotential reward second := by
  have hsets : (AdmissibleRelation reward).chargesFrom first =
      (AdmissibleRelation reward).chargesFrom second := by
    apply Set.Subset.antisymm
    · exact chargesFrom_subset_of_payoff_eq first second hpayoff
    · exact chargesFrom_subset_of_payoff_eq second first hpayoff.symm
  unfold quittingPunishmentFloorAdmissiblePotential ChargedRelation.value
  rw [hsets]

/-! ## Canonical one-owner funding roots -/

omit [Fintype ι] in
/-- A one-owner root with hazard strictly between zero and one has precisely
that owner as its interior support. -/
theorem isQuittingRootInteriorOnSupport_sureSetOwnerRoot_empty
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuittingRootInteriorOnSupport
      (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner} := by
  constructor
  · intro who hwho
    have hwho' : who = owner := by simpa using hwho
    subst who
    simpa [hazardOfRoot, quittingSureSetOwnerRoot] using And.intro hp0 hp1
  · intro who hwho
    have hne : who ≠ owner := by simpa using hwho
    simp [hazardOfRoot, quittingSureSetOwnerRoot, quittingPureSetRoot,
      quittingSetAction, Function.update, hne]

/-- The literal absorption mass of the strictly mixed one-owner root is its
hazard. -/
theorem quittingRootAbsorptionMass_sureSetOwnerRoot_empty
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootAbsorptionMass
      (quittingSureSetOwnerRoot ∅ owner p hp0 hp1) = p := by
  unfold quittingRootAbsorptionMass
  rw [stationaryContinueMass_sureSetOwnerRoot_empty]
  ring

omit [DecidableEq ι] in
/-- The aggregate positive-singleton terminal debt uses only diagonal
coordinates of singleton reward rows, so it is bounded by the canonical
sum-of-all-absolute-rewards bound itself, without a player-cardinality
factor. -/
theorem sum_positiveSingletonDebtCap_le_quittingRewardBound :
    (∑ who, quittingPositiveSingletonDebtCap reward who) ≤
      quittingRewardBound reward := by
  classical
  let row : {S : Finset ι // S.Nonempty} → ℝ :=
    fun terminal ↦ ∑ who, |reward terminal who|
  have hinjective : Function.Injective
      (quittingSingletonTerminal : ι → {S : Finset ι // S.Nonempty}) := by
    intro first second heq
    have hval : ({first} : Finset ι) = {second} :=
      congrArg Subtype.val heq
    simpa using hval
  have hdiagonal : (∑ who, quittingPositiveSingletonDebtCap reward who) ≤
      ∑ who, row (quittingSingletonTerminal who) := by
    apply Finset.sum_le_sum
    intro who _
    calc
      quittingPositiveSingletonDebtCap reward who ≤
          |reward (quittingSingletonTerminal who) who| := by
        unfold quittingPositiveSingletonDebtCap
        exact max_le (abs_nonneg _) (le_abs_self _)
      _ ≤ row (quittingSingletonTerminal who) := by
        exact Finset.single_le_sum
          (fun player _ ↦
            abs_nonneg (reward (quittingSingletonTerminal who) player))
          (Finset.mem_univ who)
  have hrows : (∑ who, row (quittingSingletonTerminal who)) ≤
      ∑ terminal, row terminal := by
    rw [← Finset.sum_image (s := (Finset.univ : Finset ι))
      (f := row) hinjective.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _)
      (fun terminal _ _ ↦ Finset.sum_nonneg
        (fun who _ ↦ abs_nonneg (reward terminal who)))
  exact hdiagonal.trans (by
    simpa [quittingRewardBound, row] using hrows)

/-- A pure singleton quitter cannot have zero Bellman target when its own
positive singleton debt cap is nonzero.  This is the exact one-stage
obstruction at the hazard-one boundary; it is independent of Nash signs. -/
theorem not_exists_zeroTarget_pureSingletonContinuation
    (owner : ι) (hcap : 0 < quittingPositiveSingletonDebtCap reward owner) :
    ¬ ∃ continuation : Payoff ι,
      (0 : Payoff ι) = quittingRootSuccessorPayoff reward continuation
        (quittingPureSetRoot {owner}) := by
  rintro ⟨continuation, hbellman⟩
  have howner := congrFun hbellman owner
  have hnonempty : ({owner} : Finset ι).Nonempty := singleton_nonempty owner
  change 0 = quittingRootExpectedPayoff reward continuation
    (quittingPureSetRoot {owner}) owner at howner
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty hnonempty,
    zero_mul, add_zero] at howner
  have hrewards : reward (quittingSingletonTerminal owner) owner = 0 := by
    simpa [quittingSetReward, quittingSingletonTerminal] using howner.symm
  rw [quittingPositiveSingletonDebtCap, hrewards, max_self] at hcap
  exact lt_irrefl 0 hcap

/-! ## Boxed states supplied by a physical frozen-root lift -/

/-- Any product root can be attached to the zero payoff as a boxed
floor-admissible state when the punishment floor is nonpositive. -/
def quittingZeroPayoffAdmissibleState
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (root : ι → PMF Bool) :
    QuittingPunishmentFloorAdmissibleState reward := by
  refine ⟨⟨((0, quittingFrozenRootLiftSimplex root)), ?_⟩, hpunishment⟩
  change (0 : Payoff ι) ∈ Set.Icc
    (fun _ => -quittingRewardBound reward)
    (fun _ => quittingRewardBound reward)
  constructor
  · intro who
    exact neg_nonpos.mpr (quittingRewardBound_nonneg reward)
  · intro who
    exact quittingRewardBound_nonneg reward

/-- The continuation side of a physical frozen-root lift is a boxed
floor-admissible state. -/
def quittingFrozenRootContinuationAdmissibleState
    (target : Payoff ι) (root : ι → PMF Bool) (support : Finset ι)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward target
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (tailRoot : QuittingRootSimplex ι) :
    QuittingPunishmentFloorAdmissibleState reward := by
  refine ⟨⟨((continuation, tailRoot)), ?_⟩, hlift.2.2.2.1⟩
  constructor
  · intro who
    exact (neg_quittingRewardBound_le_quittingPunishmentValue reward who).trans
      (hlift.2.2.2.1 who)
  · exact hlift.2.2.2.2

/-! ## Intrinsic finite-chronology nonnegativity and saturation -/

namespace QuittingFiniteDynamicDebtAdmissibleChronology

variable {cutoff : ℕ}
variable (path : QuittingFiniteNashBellmanPath ι cutoff)

/-- Aggregate diagonal debt source is nonnegative at every displayed point. -/
theorem source_nonneg
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) :
    0 ≤ source (reward := reward) path time := by
  unfold source
  exact Finset.sum_nonneg (fun who _ ↦
    quittingDynamicDebtSeam_nonneg
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time)
      (quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
        reward cutoff path hpath time) who)

/-- Aggregate exact debt is nonnegative at every displayed point. -/
theorem debt_nonneg
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) :
    0 ≤ debt (reward := reward) path time := by
  unfold debt
  exact Finset.sum_nonneg (fun who _ ↦
    (quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward cutoff path hpath time).2.1 who)

/-- Saturation of the universal `card * rewardBound` estimate forces every
player's positive singleton cap to attain the reward bound.  Thus, when the
scale is positive, every such cap is strictly positive. -/
theorem positiveSingletonDebtCap_pos_of_terminalDebt_eq_scale
    (hscale : 0 < (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (hsaturated : debt (reward := reward) path cutoff =
      (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (owner : ι) :
    0 < quittingPositiveSingletonDebtCap reward owner := by
  have hcap_le (who : ι) :
      quittingPositiveSingletonDebtCap reward who ≤
        quittingRewardBound reward :=
    (le_abs_self _).trans
      (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
  have hsum : (∑ who, quittingPositiveSingletonDebtCap reward who) =
      (Fintype.card ι : ℝ) * quittingRewardBound reward := by
    rw [← debt_cutoff_eq_sum_positiveSingletonDebtCap path]
    exact hsaturated
  have howner_eq : quittingPositiveSingletonDebtCap reward owner =
      quittingRewardBound reward := by
    apply le_antisymm (hcap_le owner)
    by_contra hnot
    have howner_lt : quittingPositiveSingletonDebtCap reward owner <
        quittingRewardBound reward := lt_of_not_ge hnot
    have hsum_lt : (∑ who, quittingPositiveSingletonDebtCap reward who) <
        ∑ _who : ι, quittingRewardBound reward := by
      apply Finset.sum_lt_sum
      · intro who _
        exact hcap_le who
      · exact ⟨owner, Finset.mem_univ owner, howner_lt⟩
    have : (∑ who, quittingPositiveSingletonDebtCap reward who) <
        (Fintype.card ι : ℝ) * quittingRewardBound reward := by
      simpa using hsum_lt
    linarith
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨owner⟩
  have hbound : 0 < quittingRewardBound reward := by
    nlinarith
  rw [howner_eq]
  exact hbound

/-- At a positive saturated terminal cap, the obvious full-charge
single-owner pure-Quit predecessor is Bellman-infeasible for every owner.
This does not exclude more complicated full-absorption product roots. -/
theorem saturated_terminalDebt_no_pureSingleton_incomingEdge
    (hscale : 0 < (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (hsaturated : debt (reward := reward) path cutoff =
      (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (owner : ι) (tailRoot : QuittingRootSimplex ι) :
    ¬ ∃ continuation : Payoff ι,
      IsQuittingNashBellmanEdge reward
        (0, quittingFrozenRootLiftSimplex (quittingPureSetRoot {owner}))
        (continuation, tailRoot) := by
  rintro ⟨continuation, hedge⟩
  apply not_exists_zeroTarget_pureSingletonContinuation owner
    (positiveSingletonDebtCap_pos_of_terminalDebt_eq_scale
      path hscale hsaturated owner)
  refine ⟨continuation, ?_⟩
  simpa [quittingRootOfSimplex_frozenRootLiftSimplex] using hedge.1

end QuittingFiniteDynamicDebtAdmissibleChronology

/-! ## Aggregate-anchor debt-source data -/

namespace QuittingAggregateCalibratedTerminalAnchor

/-- Enriched exact debt-source flow of one displayed finite anchor edge. -/
def debtSourceFlow
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (time : ℕ) :
    RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι) :=
  quittingDebtSourceObstructionFlow
    (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward (anchor.last + 1) anchor.path time,
      quittingFiniteNashBellmanPathDynamicDebtPoint
        reward (anchor.last + 1) anchor.path (time + 1))

/-- One finite anchor edge lies simultaneously in every playerwise
debt-source zero face of the exact counterexample carrier. -/
def IsAllDebtSourceZeroFace
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (time : ℕ) : Prop :=
  ∀ selected, anchor.debtSourceFlow time ∈
    exposedFace (quittingDebtSourceZeroFaceCostate selected)
      (quittingDebtSourceOneStageObstructionCarrier reward)

/-- Every calibrated positive-debt anchor has strictly positive aggregate
terminal cap.  Its marked positive initial debt is already bounded by the
same player's singleton cap. -/
theorem terminalAggregateDebt_pos
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    0 < ∑ who, quittingPositiveSingletonDebtCap reward who := by
  have hownerCap :
      quittingFiniteNashBellmanPathDynamicDebt
          reward (anchor.last + 1) anchor.path anchor.owner 0 ≤
        quittingPositiveSingletonDebtCap reward anchor.owner :=
    quittingFiniteNashBellmanPathDynamicDebt_le_cap
      reward (anchor.last + 1) anchor.path anchor.path_mem anchor.owner 0
        (by omega)
  have hcapPos : 0 < quittingPositiveSingletonDebtCap reward anchor.owner :=
    anchor.ownerDebt_pos.trans_le hownerCap
  exact hcapPos.trans_le
    (Finset.single_le_sum
      (fun who _ ↦ le_max_left 0
        (reward (quittingSingletonTerminal who) who))
      (Finset.mem_univ anchor.owner))

end QuittingAggregateCalibratedTerminalAnchor

/-! ## Sharp scalar regression for the remaining initial slack -/

/-- Terminal domination plus exact killed debt recursion and the stronger
additive capacity recursion do not force a zero source.  This one-edge finite
regression has a tightly funded terminal boundary, but positive initial
capacity slack absorbs a strictly positive source. -/
theorem fundedTerminalBoundary_does_not_force_zeroSource_regression :
    let survival : ℝ := 1 / 2
    let source : ℝ := 1
    let terminalDebt : ℝ := 1
    let initialDebt : ℝ := 3 / 2
    let terminalAccount : ℝ := 1
    let initialAccount : ℝ := 2
    0 ≤ survival ∧ survival ≤ 1 ∧
      initialDebt = source + survival * terminalDebt ∧
      initialAccount = source + terminalAccount ∧
      terminalDebt ≤ terminalAccount ∧
      initialDebt < initialAccount ∧ 0 < source := by
  norm_num

end GameTheory
