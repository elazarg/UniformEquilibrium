/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PaidMixedDeletedResidualRegression

/-!
# Source-matching barrier at a pure deleted Nash cell

A paid strict-mixed large-base cell need not retain its paid leave premium at
any pure Nash cell after deleting the other base label.  The counterexample is
an actual four-player quitting reward table, not an abstract pair of binary
rows.  Thus the remaining pure/boundary chamber needs an additional
source-matching field; existence of a deleted pure Nash point alone cannot
close it.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

/-- Four-player reward table separating the original paid mixed root from the
unique pure Nash cell after deletion.  Labels `0,1,2,3` are respectively the
retained owner, the paid base label, and the two free labels. -/
def paidMixedPureDeletedNashBarrierReward :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun S who =>
    if who = 2 then
      if 2 ∈ S.1 then
        if 1 ∈ S.1 then (if 3 ∈ S.1 then -1 else 1) else 1
      else 0
    else if who = 3 then
      if 3 ∈ S.1 then
        if 1 ∈ S.1 then (if 2 ∈ S.1 then 1 else -1) else 1
      else 0
    else if who = 1 then
      if 1 ∈ S.1 then 0
      else if 2 ∈ S.1 then -1 else if 3 ∈ S.1 then -1 else 8
    else 0

/-- The original two-free-player rows form strict matching pennies. -/
theorem paidMixedPureDeletedNashBarrierReward_originalRows :
    quittingLargeBaseFirstRow paidMixedPureDeletedNashBarrierReward
        {0, 1} {2, 3} 2 3 = (fun action => if action then -1 else 1) ∧
      quittingLargeBaseSecondRow paidMixedPureDeletedNashBarrierReward
        {0, 1} {2, 3} 2 3 = (fun action => if action then 1 else -1) := by
  have hrows := quittingLargeBaseRows_eq_purePaidRows
    paidMixedPureDeletedNashBarrierReward (1 : Fin 4) 0 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show ({1, 0} : Finset (Fin 4)) = {0, 1} by
    ext who
    simp [or_comm]] at hrows
  constructor
  · rw [hrows.1]
    funext action
    cases action <;>
      simp [paidMixedPureDeletedNashBarrierReward,
        purePaidOriginalCoalition, purePaidDeletedCoalition,
        purePaidRetainedSet, quittingSetReward]
  · rw [hrows.2]
    funext action
    cases action <;>
      simp [paidMixedPureDeletedNashBarrierReward,
        purePaidOriginalCoalition, purePaidDeletedCoalition,
        purePaidRetainedSet, quittingSetReward]

/-- After deleting the paid base label, both free players strictly prefer
Quit at every opponent action. -/
theorem paidMixedPureDeletedNashBarrierReward_deletedRows :
    quittingLargeBaseDeletedFirstRow paidMixedPureDeletedNashBarrierReward
        0 {2, 3} 2 3 = (fun _ => 1) ∧
      quittingLargeBaseDeletedSecondRow paidMixedPureDeletedNashBarrierReward
        0 {2, 3} 2 3 = (fun _ => 1) := by
  constructor <;> funext action <;> cases action
  · rw [show quittingLargeBaseDeletedFirstRow
        paidMixedPureDeletedNashBarrierReward 0 {2, 3} 2 3 false =
      quittingRootEndpointDifference paidMixedPureDeletedNashBarrierReward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition 0 2 3 false false)) 2 by
      unfold quittingLargeBaseDeletedFirstRow quittingLargeBaseFirstRow
      rw [← quittingRootEndpointDifference_update_self
        paidMixedPureDeletedNashBarrierReward 0 _ 2 (PMF.pure false)]
      congr 1
      funext who
      fin_cases who <;>
        simp [quittingLargeBaseReferenceRoot, quittingPersistentBaseRoot,
          quittingPersistentBaseRootOfProfile, quittingPureSetRoot,
          quittingSetAction, purePaidDeletedCoalition, purePaidRetainedSet]]
    rw [quittingRootEndpointDifference_purePaidDeleted_first
      paidMixedPureDeletedNashBarrierReward (by decide) (by decide)]
    simp [purePaidDeletedFirstDifference,
      paidMixedPureDeletedNashBarrierReward, purePaidDeletedCoalition,
      purePaidRetainedSet, quittingSetReward]
  · rw [show quittingLargeBaseDeletedFirstRow
        paidMixedPureDeletedNashBarrierReward 0 {2, 3} 2 3 true =
      quittingRootEndpointDifference paidMixedPureDeletedNashBarrierReward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition 0 2 3 false true)) 2 by
      unfold quittingLargeBaseDeletedFirstRow quittingLargeBaseFirstRow
      rw [← quittingRootEndpointDifference_update_self
        paidMixedPureDeletedNashBarrierReward 0 _ 2 (PMF.pure false)]
      congr 1
      funext who
      fin_cases who <;>
        simp [quittingLargeBaseReferenceRoot, quittingPersistentBaseRoot,
          quittingPersistentBaseRootOfProfile, quittingPureSetRoot,
          quittingSetAction, purePaidDeletedCoalition, purePaidRetainedSet]]
    rw [quittingRootEndpointDifference_purePaidDeleted_first
      paidMixedPureDeletedNashBarrierReward (by decide) (by decide)]
    simp [purePaidDeletedFirstDifference,
      paidMixedPureDeletedNashBarrierReward, purePaidDeletedCoalition,
      purePaidRetainedSet, quittingSetReward]
  · rw [show quittingLargeBaseDeletedSecondRow
        paidMixedPureDeletedNashBarrierReward 0 {2, 3} 2 3 false =
      quittingRootEndpointDifference paidMixedPureDeletedNashBarrierReward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition 0 2 3 false false)) 3 by
      unfold quittingLargeBaseDeletedSecondRow quittingLargeBaseSecondRow
      rw [← quittingRootEndpointDifference_update_self
        paidMixedPureDeletedNashBarrierReward 0 _ 3 (PMF.pure false)]
      congr 1
      funext who
      fin_cases who <;>
        simp [quittingLargeBaseReferenceRoot, quittingPersistentBaseRoot,
          quittingPersistentBaseRootOfProfile, quittingPureSetRoot,
          quittingSetAction, purePaidDeletedCoalition, purePaidRetainedSet]]
    rw [quittingRootEndpointDifference_purePaidDeleted_second
      paidMixedPureDeletedNashBarrierReward (by decide) (by decide)]
    simp [purePaidDeletedSecondDifference,
      paidMixedPureDeletedNashBarrierReward, purePaidDeletedCoalition,
      purePaidRetainedSet, quittingSetReward]
  · rw [show quittingLargeBaseDeletedSecondRow
        paidMixedPureDeletedNashBarrierReward 0 {2, 3} 2 3 true =
      quittingRootEndpointDifference paidMixedPureDeletedNashBarrierReward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition 0 2 3 true false)) 3 by
      unfold quittingLargeBaseDeletedSecondRow quittingLargeBaseSecondRow
      rw [← quittingRootEndpointDifference_update_self
        paidMixedPureDeletedNashBarrierReward 0 _ 3 (PMF.pure false)]
      congr 1
      funext who
      fin_cases who <;>
        simp [quittingLargeBaseReferenceRoot, quittingPersistentBaseRoot,
          quittingPersistentBaseRootOfProfile, quittingPureSetRoot,
          quittingSetAction, purePaidDeletedCoalition, purePaidRetainedSet]]
    rw [quittingRootEndpointDifference_purePaidDeleted_second
      paidMixedPureDeletedNashBarrierReward (by decide) (by decide)]
    simp [purePaidDeletedSecondDifference,
      paidMixedPureDeletedNashBarrierReward, purePaidDeletedCoalition,
      purePaidRetainedSet, quittingSetReward]

/-- The paid leave observable is positive only at the cell that the deleted
best replies reject, and is negative at the unique deleted Nash cell. -/
theorem paidMixedPureDeletedNashBarrierReward_leaveCells
    (firstAction secondAction : Bool) :
    quittingLargeBaseLeaveCell paidMixedPureDeletedNashBarrierReward
        {0, 1} {2, 3} 2 3 1 firstAction secondAction =
      if firstAction = false ∧ secondAction = false then 8 else -1 := by
  rw [show ({0, 1} : Finset (Fin 4)) = {1, 0} by
    ext who
    simp [or_comm]]
  rw [quittingLargeBaseLeaveCell_eq_purePaidLeave
    paidMixedPureDeletedNashBarrierReward (1 : Fin 4) 0 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  cases firstAction <;> cases secondAction <;>
    simp [paidMixedPureDeletedNashBarrierReward,
      purePaidOriginalCoalition, purePaidDeletedCoalition,
      purePaidRetainedSet, quittingSetReward]

/-- **Sharp source-matching obstruction.**  The original actual rows have a
strict mixed Nash point whose paid cleared leave observable exceeds the
positive threshold `1`.  The deleted actual rows have a pure Nash point, but
every such point is `(Quit,Quit)`, where the paid leave premium is negative.
Therefore a producer that merely chooses an arbitrary deleted pure Nash point
cannot attach the original paid mixed source to the pure/repaired compiler. -/
theorem exists_actual_paidMixed_with_no_paid_deletedPureNash :
    let reward := paidMixedPureDeletedNashBarrierReward
    let alpha := quittingLargeBaseFirstRow reward {0, 1} {2, 3} 2 3
    let beta := quittingLargeBaseSecondRow reward {0, 1} {2, 3} 2 3
    let deletedAlpha := quittingLargeBaseDeletedFirstRow reward 0 {2, 3} 2 3
    let deletedBeta := quittingLargeBaseDeletedSecondRow reward 0 {2, 3} 2 3
    IsStrictMatchingPenniesOrientation alpha beta ∧
      binaryClearedDenominator alpha beta ≤
        binaryClearedObservable alpha beta
          (quittingLargeBaseLeaveCell reward {0, 1} {2, 3} 2 3 1) ∧
      (∃ firstAction secondAction,
        IsPureBinaryDifferenceNash deletedAlpha deletedBeta
          firstAction secondAction) ∧
      ∀ firstAction secondAction,
        IsPureBinaryDifferenceNash deletedAlpha deletedBeta
            firstAction secondAction →
          quittingLargeBaseLeaveCell reward {0, 1} {2, 3} 2 3 1
            firstAction secondAction < 0 := by
  dsimp only
  rw [paidMixedPureDeletedNashBarrierReward_originalRows.1,
    paidMixedPureDeletedNashBarrierReward_originalRows.2,
    paidMixedPureDeletedNashBarrierReward_deletedRows.1,
    paidMixedPureDeletedNashBarrierReward_deletedRows.2]
  refine ⟨?_, ?_, ⟨true, true, by simp [IsPureBinaryDifferenceNash]⟩, ?_⟩
  · exact Or.inl (by norm_num)
  · norm_num [binaryClearedDenominator, binaryClearedObservable,
      paidMixedPureDeletedNashBarrierReward_leaveCells]
  · intro firstAction secondAction hnash
    have hfirst : firstAction = true := by
      cases firstAction
      · norm_num [IsPureBinaryDifferenceNash] at hnash
      · rfl
    have hsecond : secondAction = true := by
      cases secondAction
      · norm_num [IsPureBinaryDifferenceNash] at hnash
      · rfl
    subst firstAction
    subst secondAction
    norm_num [paidMixedPureDeletedNashBarrierReward_leaveCells]

/-- The obstruction is not an artifact of selecting the wrong pure Nash
cell: the deleted binary game has a unique product Nash rate, namely
`(1,1)`, and the paid leave observable at that rate is exactly `-1`. -/
theorem paidMixedPureDeletedNashBarrier_all_deletedNash_bad :
    let reward := paidMixedPureDeletedNashBarrierReward
    let deletedAlpha := quittingLargeBaseDeletedFirstRow reward 0 {2, 3} 2 3
    let deletedBeta := quittingLargeBaseDeletedSecondRow reward 0 {2, 3} 2 3
    ∀ firstRate secondRate,
      IsBinaryDifferenceNash deletedAlpha deletedBeta firstRate secondRate →
        firstRate = 1 ∧ secondRate = 1 ∧
          binaryProductExpectation
            (quittingLargeBaseLeaveCell reward {0, 1} {2, 3} 2 3 1)
              firstRate secondRate = -1 := by
  dsimp only
  rw [paidMixedPureDeletedNashBarrierReward_deletedRows.1,
    paidMixedPureDeletedNashBarrierReward_deletedRows.2]
  intro firstRate secondRate hnash
  have hfirst : firstRate = 1 := by
    rcases hnash with ⟨hfirstBounds, _hsecondBounds, hcontinue, _⟩
    simp [binaryFirstDifference] at hcontinue
    exact le_antisymm hfirstBounds.2 (by linarith)
  have hsecond : secondRate = 1 := by
    rcases hnash with
      ⟨_hfirstBounds, hsecondBounds, _, _, hcontinue, _⟩
    simp [binarySecondDifference] at hcontinue
    exact le_antisymm hsecondBounds.2 (by linarith)
  subst firstRate
  subst secondRate
  refine ⟨rfl, rfl, ?_⟩
  norm_num [binaryProductExpectation,
    paidMixedPureDeletedNashBarrierReward_leaveCells]

end GameTheory
