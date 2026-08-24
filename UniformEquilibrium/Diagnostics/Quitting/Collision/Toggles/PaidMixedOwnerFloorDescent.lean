/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PaidChainSupportTwoAggregate

/-!
# Paid-mixed owner-floor descent

The positive owner-floor face of the actual paid-mixed support-two residue is
not terminal.  Its strict matching-pennies weights form an actual repaired
four-cell source, so the existing deterministic-cell descent applies.  The
only paid-mixed faces left here are the two nonzero deletion residuals.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal cleared mass of a Boolean cell in a strict matching-pennies
product law. -/
def binaryClearedCellWeight (alpha beta : Bool → ℝ) : Bool → Bool → ℝ
  | false, false => -beta true * alpha true
  | true, false => beta false * alpha true
  | false, true => beta true * alpha false
  | true, true => -beta false * alpha false

theorem binaryClearedCellWeight_pos
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (firstAction secondAction : Bool) :
    0 < binaryClearedCellWeight alpha beta firstAction secondAction := by
  rcases orientation with orientation | orientation <;>
    rcases orientation with ⟨ha0, ha1, hb1, hb0⟩ <;>
    cases firstAction <;> cases secondAction <;>
    simp only [binaryClearedCellWeight] <;> nlinarith

theorem binaryClearedCellWeight_sum (alpha beta : Bool → ℝ) :
    repairedFourCellWeightedSum (binaryClearedCellWeight alpha beta)
        (fun _ _ ↦ 1) =
      binaryClearedDenominator alpha beta := by
  rw [show repairedFourCellWeightedSum (binaryClearedCellWeight alpha beta)
      (fun _ _ ↦ 1) =
      -beta true * alpha true + beta false * alpha true +
        beta true * alpha false + -beta false * alpha false by
    simp [repairedFourCellWeightedSum, binaryClearedCellWeight]]
  exact binaryClearedWeights_sum alpha beta

/-- The strict mixed weights, with the deleted paid label fixed at Continue,
form the repaired source needed by deterministic-cell selection. -/
def paidMixedOwnerFloorRepairedSource
    (owner paid first second : ι)
    (labels : RepairedResidualFourLabels owner paid first second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    RepairedResidualPureExitSource owner paid first second false where
  labels := labels
  weight := binaryClearedCellWeight alpha beta
  denominator := binaryClearedDenominator alpha beta
  weight_nonneg := fun firstAction secondAction =>
    (binaryClearedCellWeight_pos orientation firstAction secondAction).le
  sum_weight := binaryClearedCellWeight_sum alpha beta
  denominator_pos := binaryClearedDenominator_pos orientation

omit [Fintype ι] in
/-- The singleton-base pure cell used in the mixed owner-floor observable is
the repaired deterministic coalition with the paid label fixed at Continue. -/
theorem quittingLargeBaseDeletedPureRoot_eq_repairedCell
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    (firstAction secondAction : Bool) :
    Function.update
        (Function.update
          (quittingLargeBaseReferenceRoot {owner} {first, second} first)
          first (PMF.pure firstAction))
        second (PMF.pure secondAction) =
      quittingPureSetRoot
        (repairedResidualCellCoalition owner paid first second false
          firstAction secondAction) := by
  rcases labels with
    ⟨hownerPaid, hownerFirst, hownerSecond, hpaidFirst, hpaidSecond,
      hfirstSecond, hexhaust⟩
  have hpaidOwner := hownerPaid.symm
  have hfirstOwner := hownerFirst.symm
  have hsecondOwner := hownerSecond.symm
  have hfirstPaid := hpaidFirst.symm
  have hsecondPaid := hpaidSecond.symm
  have hsecondFirst := hfirstSecond.symm
  funext who
  rcases hexhaust who with howner | hpaid | hfirst | hsecond <;>
    subst who <;> cases firstAction <;> cases secondAction <;>
    simp_all [quittingLargeBaseReferenceRoot, quittingPersistentBaseRoot,
      quittingPersistentBaseRootOfProfile, quittingPureSetRoot,
      quittingSetAction, repairedResidualCellCoalition]

/-- Cellwise identification of the actual mixed owner-floor observable with
the repaired source's piecewise owner-floor score. -/
theorem quittingLargeBaseDeletedOwnerFloorCell_eq_repaired
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    (firstAction secondAction : Bool) :
    quittingLargeBaseDeletedOwnerFloorCell reward owner {first, second}
        first second firstAction secondAction =
      repairedResidualOwnerFloorExcess reward owner paid first second false
        firstAction secondAction := by
  rw [quittingLargeBaseDeletedOwnerFloorCell,
    quittingLargeBaseDeletedPureRoot_eq_repairedCell labels]
  let cell := repairedResidualCellCoalition owner paid first second false
    firstAction secondAction
  have howner :
      quittingPureSetRoot cell owner = PMF.pure true := by
    simp [cell, repairedResidualCellCoalition, quittingPureSetRoot,
      quittingSetAction]
  rw [← quittingSingletonBaseOwnerFloorExcess_eq_neg_endpoint_of_sureQuit
    reward owner (quittingPureSetRoot cell) howner]
  have hcell : cell = purePaidDeletedCoalition owner first second
      firstAction secondAction := by
    simp [cell, repairedResidualCellCoalition, purePaidDeletedCoalition,
      purePaidRetainedSet]
  rw [hcell,
    quittingSingletonBaseOwnerFloorExcess_purePaidDeleted_eq reward
      labels.owner_ne_first labels.owner_ne_second]
  have hdeleted : (purePaidDeletedCoalition owner first second
      firstAction secondAction).Nonempty := by
    exact ⟨owner, owner_mem_purePaidDeletedCoalition owner first second
      firstAction secondAction⟩
  unfold purePaidOwnerFloorExcess
  dsimp only
  rw [quittingSetReward_of_nonempty reward hdeleted]
  cases firstAction <;> cases secondAction <;>
    simp [repairedResidualOwnerFloorExcess,
      repairedResidualWithoutOwner, repairedResidualCellCoalition,
      purePaidRetainedSet, labels.owner_ne_first,
      labels.owner_ne_second]
  all_goals
    congr 2

/-- The repaired source numerator is exactly the displayed cleared owner-floor
observable of the paid-mixed residue. -/
theorem paidMixedOwnerFloorRepairedSource_numerator_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    (alpha beta : Bool → ℝ)
    (orientation : IsStrictMatchingPenniesOrientation alpha beta) :
    (paidMixedOwnerFloorRepairedSource owner paid first second labels
      alpha beta orientation).ownerFloorNumerator reward =
      binaryClearedObservable alpha beta
        (quittingLargeBaseDeletedOwnerFloorCell reward owner {first, second}
          first second) := by
  simp only [RepairedResidualPureExitSource.ownerFloorNumerator,
    repairedFourCellWeightedSum, paidMixedOwnerFloorRepairedSource,
    binaryClearedCellWeight, binaryClearedObservable]
  rw [quittingLargeBaseDeletedOwnerFloorCell_eq_repaired reward labels false false,
    quittingLargeBaseDeletedOwnerFloorCell_eq_repaired reward labels true false,
    quittingLargeBaseDeletedOwnerFloorCell_eq_repaired reward labels false true,
    quittingLargeBaseDeletedOwnerFloorCell_eq_repaired reward labels true true]

/-- The positive owner-floor obstruction in the paid-mixed arm descends all
the way to a deterministic nonowner toggle (with the empty punishment cell
already dispatched). -/
theorem QuittingTerminalExploitabilityWitness.paidMixedOwnerFloorFiniteResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4)
    {owner paid first second : ι}
    (labels : RepairedResidualFourLabels owner paid first second)
    {alpha beta : Bool → ℝ}
    (orientation : IsStrictMatchingPenniesOrientation alpha beta)
    (positive : 0 < binaryClearedObservable alpha beta
      (quittingLargeBaseDeletedOwnerFloorCell reward owner {first, second}
        first second)) :
    HasRepairedPureExitFiniteResidual reward
      (paidMixedOwnerFloorRepairedSource owner paid first second labels
        alpha beta orientation) := by
  right
  apply witness.repairedOwnerFloorResidual_withoutEmpty hcard
  rw [paidMixedOwnerFloorRepairedSource_numerator_eq]
  exact positive

/-- The owner-floor face retains the literal mixed weights and labels while
recording its deterministic-cell output. -/
def HasPaidMixedOwnerFloorFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner paid first second : ι) (alpha beta : Bool → ℝ) : Prop :=
  ∃ (orientation : IsStrictMatchingPenniesOrientation alpha beta)
      (labels : RepairedResidualFourLabels owner paid first second),
    HasRepairedPureExitFiniteResidual reward
      (paidMixedOwnerFloorRepairedSource owner paid first second labels
        alpha beta orientation)

omit [Fintype ι] in
/-- Four actual support-two labels in either paid/owner order give the label
package used by the mixed repaired source. -/
theorem repairedResidualFourLabels_of_supportTwoPair
    (baseFirst baseSecond first second paid owner : ι)
    (hbaseNe : baseFirst ≠ baseSecond) (hfreeNe : first ≠ second)
    (hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      ({first, second} : Finset ι))
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (hpair : (paid = baseFirst ∧ owner = baseSecond) ∨
      (paid = baseSecond ∧ owner = baseFirst)) :
    RepairedResidualFourLabels owner paid first second := by
  have cross {basePlayer freePlayer : ι}
      (hbase : basePlayer ∈ ({baseFirst, baseSecond} : Finset ι))
      (hfree : freePlayer ∈ ({first, second} : Finset ι)) :
      basePlayer ≠ freePlayer := by
    intro equality
    subst freePlayer
    exact Finset.disjoint_left.mp hdisjoint hbase hfree
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact {
      owner_ne_remaining := hbaseNe.symm
      owner_ne_first := cross (by simp) (by simp)
      owner_ne_second := cross (by simp) (by simp)
      remaining_ne_first := cross (by simp) (by simp)
      remaining_ne_second := cross (by simp) (by simp)
      first_ne_second := hfreeNe
      exhaust := fun who => by
        rcases hexhaust who with hbaseFirst | hbaseSecond | hfirst | hsecond
        · exact Or.inr (Or.inl hbaseFirst)
        · exact Or.inl hbaseSecond
        · exact Or.inr (Or.inr (Or.inl hfirst))
        · exact Or.inr (Or.inr (Or.inr hsecond)) }
  · exact {
      owner_ne_remaining := hbaseNe
      owner_ne_first := cross (by simp) (by simp)
      owner_ne_second := cross (by simp) (by simp)
      remaining_ne_first := cross (by simp) (by simp)
      remaining_ne_second := cross (by simp) (by simp)
      first_ne_second := hfreeNe
      exhaust := fun who => by
        rcases hexhaust who with hbaseFirst | hbaseSecond | hfirst | hsecond
        · exact Or.inl hbaseFirst
        · exact Or.inr (Or.inl hbaseSecond)
        · exact Or.inr (Or.inr (Or.inl hfirst))
        · exact Or.inr (Or.inr (Or.inr hsecond)) }

/-- Strengthened paid-mixed residue: the positive owner-floor face has been
eliminated into its deterministic-cell compiler, leaving only the two
source-linked nonzero deletion residuals as numerical obstructions. -/
def HasActualPaidMixedFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseFirst baseSecond first second : ι) (gamma : ℝ) : Prop :=
  let base : Finset ι := {baseFirst, baseSecond}
  let free : Finset ι := {first, second}
  let alpha := quittingLargeBaseFirstRow reward base free first second
  let beta := quittingLargeBaseSecondRow reward base free first second
  ∃ paid owner,
    ((paid = baseFirst ∧ owner = baseSecond) ∨
      (paid = baseSecond ∧ owner = baseFirst)) ∧
    IsStrictMatchingPenniesOrientation alpha beta ∧
    gamma * binaryClearedDenominator alpha beta ≤
      binaryClearedObservable alpha beta
        (quittingLargeBaseLeaveCell reward base free first second paid) ∧
    (binaryDeletedFirstResidual alpha
          (quittingLargeBaseDeletedFirstRow reward owner free first second) ≠ 0 ∨
      binaryDeletedSecondResidual beta
          (quittingLargeBaseDeletedSecondRow reward owner free first second) ≠ 0 ∨
      HasPaidMixedOwnerFloorFiniteResidual reward owner paid first second
        alpha beta)

/-- The old three-face numerical mixed residue contracts by a whole face: a
positive owner-floor numerator is compiled to deterministic-cell toggles. -/
theorem QuittingTerminalExploitabilityWitness.hasActualPaidMixedFiniteResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4)
    (baseFirst baseSecond first second : ι)
    (hbaseNe : baseFirst ≠ baseSecond) (hfreeNe : first ≠ second)
    (hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      ({first, second} : Finset ι))
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (gamma : ℝ)
    (residual : HasActualPaidMixedDeletionResidual reward baseFirst baseSecond
      first second gamma) :
    HasActualPaidMixedFiniteResidual reward baseFirst baseSecond first second
      gamma := by
  dsimp [HasActualPaidMixedDeletionResidual] at residual
  dsimp [HasActualPaidMixedFiniteResidual]
  obtain ⟨paid, owner, hpair, orientation, hpaid, hresidual⟩ := residual
  refine ⟨paid, owner, hpair, orientation, hpaid, ?_⟩
  rcases hresidual with hfirst | hsecond | hfloor
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond)
  · right
    right
    let labels := repairedResidualFourLabels_of_supportTwoPair
      baseFirst baseSecond first second paid owner hbaseNe hfreeNe hdisjoint
        hexhaust hpair
    exact ⟨orientation, labels,
      witness.paidMixedOwnerFloorFiniteResidual hcard labels orientation
        hfloor⟩

/-- Final support-two paid-chain output with the mixed owner-floor face also
compiled. -/
def HasSupportTwoPaidChainCompiledResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseFirst baseSecond first second : ι) (gamma : ℝ) : Prop :=
  (∃ paid owner firstAction secondAction,
    ((paid = baseFirst ∧ owner = baseSecond) ∨
      (paid = baseSecond ∧ owner = baseFirst)) ∧
    HasPurePaidChainFiniteResidual reward paid owner first second
      firstAction secondAction) ∨
  HasActualPaidMixedFiniteResidual reward baseFirst baseSecond first second gamma

/-- The actual support-two gap contracts to the fully compiled pure chain or
to the paid-mixed residue with only its two deletion faces still numerical. -/
theorem QuittingTerminalExploitabilityWitness.hasSupportTwoPaidChainCompiledResidual
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4)
    (baseFirst baseSecond first second : ι)
    (hbaseNe : baseFirst ≠ baseSecond) (hfreeNe : first ≠ second)
    (hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      ({first, second} : Finset ι))
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (gap : ∀ point ∈ quittingPersistentBaseNashSet reward
        {baseFirst, baseSecond} {first, second},
      gamma ≤ quittingPersistentLargeBaseExcess reward
        {baseFirst, baseSecond} {first, second} point) :
    HasSupportTwoPaidChainCompiledResidual reward baseFirst baseSecond first
      second gamma := by
  rcases witness.hasSupportTwoPaidChainResidual hcard baseFirst baseSecond first
      second hbaseNe hfreeNe hdisjoint hexhaust gamma hgamma gap with
    hpure | hmixed
  · exact Or.inl hpure
  · exact Or.inr (witness.hasActualPaidMixedFiniteResidual hcard
      baseFirst baseSecond first second hbaseNe hfreeNe hdisjoint hexhaust
        gamma hmixed)

end GameTheory
