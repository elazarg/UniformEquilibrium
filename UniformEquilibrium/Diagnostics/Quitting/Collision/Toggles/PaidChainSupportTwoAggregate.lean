/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.EmptyPunishmentPremiumOwnerJoin
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseActualAdapter

/-!
# Support-two paid-chain aggregate

This module connects the actual two-by-two large-base dispatch to the
source-native pure-paid chain and isolates the exact mixed-deletion residue
which survives under a terminal exploitability witness.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The literal pure cell used by first-sign re-equilibration is the repaired
cell after converting the retained player's switch bit to its actual action. -/
theorem PurePaidBaseLeaveSource.firstFailure_cellRoot_eq_repairedCell
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (paidAction switched : Bool) :
    Function.update
        (Function.update
          (quittingPureSetRoot
            (purePaidDeletedCoalition owner first second
              firstQuits secondQuits))
          paid (PMF.pure paidAction))
        first (PMF.pure (Bool.xor firstQuits switched)) =
      quittingPureSetRoot
        (repairedResidualCellCoalition owner second paid first
          secondQuits paidAction (Bool.xor firstQuits switched)) := by
  rcases source with
    ⟨hpaidOwner, hpaidFirst, hpaidSecond, hownerFirst, hownerSecond,
      hfirstSecond, hcover, _hnash, _hgamma, _hpaid⟩
  have hownerPaid := hpaidOwner.symm
  have hfirstPaid := hpaidFirst.symm
  have hsecondPaid := hpaidSecond.symm
  have hfirstOwner := hownerFirst.symm
  have hsecondOwner := hownerSecond.symm
  have hsecondFirst := hfirstSecond.symm
  funext who
  rcases hcover who with hpaid | howner | hfirst | hsecond <;>
    subst who <;> cases firstQuits <;> cases secondQuits <;>
    cases paidAction <;> cases switched <;>
    simp_all [repairedResidualCellCoalition, purePaidDeletedCoalition,
      purePaidRetainedSet, quittingPureSetRoot, quittingSetAction]

omit [Fintype ι] in
/-- At a four-label large-base cell, replacing both free coordinates by pure
actions gives exactly the corresponding deterministic exit coalition. -/
theorem quittingLargeBasePureRoot_eq_purePaidOriginal
    (paid owner first second : ι)
    (_hpaidOwner : paid ≠ owner) (hpaidFirst : paid ≠ first)
    (hpaidSecond : paid ≠ second) (hownerFirst : owner ≠ first)
    (hownerSecond : owner ≠ second) (hfirstSecond : first ≠ second)
    (firstAction secondAction : Bool) :
    Function.update
        (Function.update
          (quittingLargeBaseReferenceRoot {paid, owner} {first, second} first)
          first (PMF.pure firstAction))
        second (PMF.pure secondAction) =
      quittingPureSetRoot
        (purePaidOriginalCoalition paid owner first second
          firstAction secondAction) := by
  cases firstAction <;> cases secondAction
  all_goals
    funext who
    by_cases hwhoPaid : who = paid
    · subst who
      simp [quittingLargeBaseReferenceRoot, purePaidOriginalCoalition,
        purePaidDeletedCoalition, purePaidRetainedSet, hpaidFirst,
        hpaidSecond, quittingPureSetRoot, quittingSetAction]
    · by_cases hwhoOwner : who = owner
      · subst who
        simp [quittingLargeBaseReferenceRoot, purePaidOriginalCoalition,
          purePaidDeletedCoalition, purePaidRetainedSet, hownerFirst,
          hownerSecond, quittingPureSetRoot, quittingSetAction]
      · by_cases hwhoFirst : who = first
        · subst who
          simp [purePaidOriginalCoalition, purePaidDeletedCoalition,
            purePaidRetainedSet, hfirstSecond, hpaidFirst.symm,
            hownerFirst.symm, quittingPureSetRoot, quittingSetAction]
        · by_cases hwhoSecond : who = second
          · subst who
            simp [purePaidOriginalCoalition, purePaidDeletedCoalition,
              purePaidRetainedSet, hfirstSecond.symm, hpaidSecond.symm,
              hownerSecond.symm, quittingPureSetRoot, quittingSetAction]
          · simp [quittingLargeBaseReferenceRoot,
              quittingPersistentBaseRoot,
              quittingPersistentBaseRootOfProfile, quittingPureSetRoot,
              quittingSetAction, purePaidOriginalCoalition,
              purePaidDeletedCoalition, purePaidRetainedSet, hwhoPaid,
              hwhoOwner, hwhoFirst, hwhoSecond]

/-- Endpoint difference at a deterministic exit set with a surviving anchor. -/
theorem quittingRootEndpointDifference_pureSet_of_erase_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (coalition : Finset ι) (who : ι)
    (herase : (coalition.erase who).Nonempty) :
    quittingRootEndpointDifference reward 0
        (quittingPureSetRoot coalition) who =
      quittingSetReward reward (insert who coalition) who -
        quittingSetReward reward (coalition.erase who) who := by
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      (0 : Payoff ι) coalition who herase]

/-- The remaining-player observer cell is exactly the repaired deterministic
endpoint difference. -/
theorem PurePaidBaseLeaveSource.firstFailure_observerCell_eq_repaired
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (paidAction switched : Bool) :
    paidSignFailureObserverCell reward 0
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits))
        paid first second firstQuits paidAction switched =
      repairedResidualRemainingDifference reward owner second paid first
        secondQuits paidAction (Bool.xor firstQuits switched) := by
  rw [paidSignFailureObserverCell,
    source.firstFailure_cellRoot_eq_repairedCell paidAction switched]
  let cell := repairedResidualCellCoalition owner second paid first
    secondQuits paidAction (Bool.xor firstQuits switched)
  have herase : (cell.erase second).Nonempty := by
    refine ⟨owner, Finset.mem_erase.mpr ⟨source.owner_ne_second, ?_⟩⟩
    exact owner_mem_repairedResidualCellCoalition owner second paid first
      secondQuits paidAction (Bool.xor firstQuits switched)
  rw [quittingRootEndpointDifference_pureSet_of_erase_nonempty
    reward cell second herase]
  unfold repairedResidualRemainingDifference repairedResidualWithoutRemaining
  change quittingSetReward reward (insert second cell) second -
      quittingSetReward reward (cell.erase second) second =
    quittingSetReward reward (insert second (cell.erase second)) second -
      quittingSetReward reward (cell.erase second) second
  congr 2
  ext who
  by_cases hwho : who = second <;> simp [hwho]

/-- The paid-sign owner-floor cell is exactly the repaired piecewise owner
floor, including the punishment-valued empty cell. -/
theorem PurePaidBaseLeaveSource.firstFailure_ownerFloorCell_eq_repaired
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (paidAction switched : Bool) :
    paidSignFailureOwnerFloorCell reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits))
        owner paid first firstQuits paidAction switched =
      repairedResidualOwnerFloorExcess reward owner second paid first
        secondQuits paidAction (Bool.xor firstQuits switched) := by
  rw [paidSignFailureOwnerFloorCell,
    source.firstFailure_cellRoot_eq_repairedCell paidAction switched]
  let cell := repairedResidualCellCoalition owner second paid first
    secondQuits paidAction (Bool.xor firstQuits switched)
  let without := cell.erase owner
  have hcell : cell.Nonempty := by
    exact ⟨owner, owner_mem_repairedResidualCellCoalition owner second paid first
      secondQuits paidAction (Bool.xor firstQuits switched)⟩
  rw [quittingSingletonBaseOwnerFloorExcess,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty hcell]
  simp only [zero_mul, add_zero]
  by_cases hwithout : without.Nonempty
  · rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      (tail := fun _ ↦ quittingPunishmentValue reward owner) cell owner]
    · simp [repairedResidualOwnerFloorExcess,
        repairedResidualWithoutOwner, cell, without, hwithout]
    · exact hwithout
  · have hwithoutEmpty : without = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hwithout
    have hcellSingleton : cell = {owner} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨owner_mem_repairedResidualCellCoalition owner second paid first
        secondQuits paidAction (Bool.xor firstQuits switched), ?_⟩
      intro who hwho
      by_contra hne
      have : who ∈ without := Finset.mem_erase.mpr ⟨hne, hwho⟩
      rw [hwithoutEmpty] at this
      simp at this
    change quittingRootContinuePayoff reward
        (fun _ ↦ quittingPunishmentValue reward owner)
          (quittingPureSetRoot cell) owner -
        quittingSetReward reward cell owner = _
    rw [hcellSingleton, quittingRootContinuePayoff_pureSingleton_eq_tail]
    simp [repairedResidualOwnerFloorExcess,
      repairedResidualWithoutOwner, cell, hcellSingleton]

omit [Fintype ι] in
/-- The four labels inherited by the repaired source after the first retained
sign fails. -/
theorem PurePaidBaseLeaveSource.firstFailureRepairedLabels
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ) :
    RepairedResidualFourLabels owner second paid first where
  owner_ne_remaining := source.owner_ne_second
  owner_ne_first := source.paid_ne_owner.symm
  owner_ne_second := source.owner_ne_first
  remaining_ne_first := source.paid_ne_second.symm
  remaining_ne_second := source.first_ne_second.symm
  first_ne_second := source.paid_ne_first
  exhaust := by
    intro who
    rcases source.exhaust who with hpaid | howner | hfirst | hsecond
    · exact Or.inr (Or.inr (Or.inl hpaid))
    · exact Or.inl howner
    · exact Or.inr (Or.inr (Or.inr hfirst))
    · exact Or.inr (Or.inl hsecond)

/-- The repaired four-cell source using the very same binary selection as the
actual paid-sign root. -/
def PurePaidBaseLeaveSource.firstFailureRepairedSource
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    {join switch : Bool → ℝ}
    (selection : PaidSignFailureBinarySelection join switch)
    (hjoinOld : join false ≤ -γ) (hswitchCleared : 0 < switch false) :
    RepairedResidualPureExitSource owner second paid first secondQuits :=
  RepairedResidualPureExitSource.ofPaidSignSelection selection firstQuits
    source.gamma_pos hjoinOld hswitchCleared
    source.firstFailureRepairedLabels

/-- The actual observer numerator is literally the repaired remaining-label
numerator, including the XOR reindex from switch bits to Quit actions. -/
theorem PurePaidBaseLeaveSource.firstFailure_remainingNumerator_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (selection : PaidSignFailureBinarySelection
      (paidSignFailureJoinRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) paid first firstQuits)
      (paidSignFailureSwitchRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) paid first firstQuits))
    (hjoinOld : paidSignFailureJoinRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second firstQuits secondQuits))
        paid first firstQuits false ≤ -γ)
    (hswitchCleared : 0 < paidSignFailureSwitchRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second firstQuits secondQuits))
        paid first firstQuits false) :
    let repaired := source.firstFailureRepairedSource selection hjoinOld
      hswitchCleared
    let hnash := selection.isBinaryDifferenceNash source.gamma_pos hjoinOld
      hswitchCleared
    let root := paidSignFailureRoot
      (quittingPureSetRoot
        (purePaidDeletedCoalition owner first second firstQuits secondQuits))
      paid first firstQuits selection.firstRate selection.secondRate
        hnash.1 hnash.2.1
    selection.denominator *
        quittingRootEndpointDifference reward 0 root second =
      repaired.remainingNumerator reward := by
  dsimp only
  let background := quittingPureSetRoot
    (purePaidDeletedCoalition owner first second firstQuits secondQuits)
  have hactual := selection.denominator_mul_observerEndpoint
    source.gamma_pos hjoinOld hswitchCleared reward 0 background
      source.paid_ne_second.symm source.first_ne_second.symm
      source.paid_ne_first
      firstQuits
  dsimp only at hactual
  simp only [PaidSignFailureBinarySelection.weightedSum] at hactual
  rw [source.firstFailure_observerCell_eq_repaired false false,
    source.firstFailure_observerCell_eq_repaired true false,
    source.firstFailure_observerCell_eq_repaired false true,
    source.firstFailure_observerCell_eq_repaired true true] at hactual
  cases firstQuits
  · simpa [PurePaidBaseLeaveSource.firstFailureRepairedSource,
      RepairedResidualPureExitSource.remainingNumerator,
      RepairedResidualPureExitSource.ofPaidSignSelection,
      repairedFourCellWeightedSum,
      PaidSignFailureBinarySelection.weightedSum, background] using hactual
  · simp [PurePaidBaseLeaveSource.firstFailureRepairedSource,
      RepairedResidualPureExitSource.remainingNumerator,
      RepairedResidualPureExitSource.ofPaidSignSelection,
      repairedFourCellWeightedSum, background] at hactual ⊢
    rw [hactual]
    ring

/-- The actual punishment-priced owner numerator is literally the repaired
owner-floor numerator, with the same XOR reindex and empty-cell convention. -/
theorem PurePaidBaseLeaveSource.firstFailure_ownerFloorNumerator_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (selection : PaidSignFailureBinarySelection
      (paidSignFailureJoinRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) paid first firstQuits)
      (paidSignFailureSwitchRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second
            firstQuits secondQuits)) paid first firstQuits))
    (hjoinOld : paidSignFailureJoinRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second firstQuits secondQuits))
        paid first firstQuits false ≤ -γ)
    (hswitchCleared : 0 < paidSignFailureSwitchRow reward
        (quittingPureSetRoot
          (purePaidDeletedCoalition owner first second firstQuits secondQuits))
        paid first firstQuits false) :
    let repaired := source.firstFailureRepairedSource selection hjoinOld
      hswitchCleared
    let hnash := selection.isBinaryDifferenceNash source.gamma_pos hjoinOld
      hswitchCleared
    let root := paidSignFailureRoot
      (quittingPureSetRoot
        (purePaidDeletedCoalition owner first second firstQuits secondQuits))
      paid first firstQuits selection.firstRate selection.secondRate
        hnash.1 hnash.2.1
    selection.denominator *
        quittingSingletonBaseOwnerFloorExcess reward owner root =
      repaired.ownerFloorNumerator reward := by
  dsimp only
  let background := quittingPureSetRoot
    (purePaidDeletedCoalition owner first second firstQuits secondQuits)
  have hactual := selection.denominator_mul_ownerFloorExcess
    source.gamma_pos hjoinOld hswitchCleared reward background
      source.paid_ne_owner.symm source.owner_ne_first source.paid_ne_first
      (by simp [background, purePaidDeletedCoalition, purePaidRetainedSet,
        quittingPureSetRoot, quittingSetAction]) firstQuits
  dsimp only at hactual
  simp only [background] at hactual
  simp only [PaidSignFailureBinarySelection.weightedSum] at hactual
  rw [source.firstFailure_ownerFloorCell_eq_repaired false false,
    source.firstFailure_ownerFloorCell_eq_repaired true false,
    source.firstFailure_ownerFloorCell_eq_repaired false true,
    source.firstFailure_ownerFloorCell_eq_repaired true true] at hactual
  cases firstQuits
  · simpa [PurePaidBaseLeaveSource.firstFailureRepairedSource,
      RepairedResidualPureExitSource.ownerFloorNumerator,
      RepairedResidualPureExitSource.ofPaidSignSelection,
      repairedFourCellWeightedSum,
      PaidSignFailureBinarySelection.weightedSum, background] using hactual
  · simp [PurePaidBaseLeaveSource.firstFailureRepairedSource,
      RepairedResidualPureExitSource.ownerFloorNumerator,
      RepairedResidualPureExitSource.ofPaidSignSelection,
      repairedFourCellWeightedSum] at hactual ⊢
    rw [hactual]
    ring

/-- Exact deterministic-cell alternatives remaining after a positive repaired
four-cell numerator is descended. -/
def HasRepairedPureExitFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed) :
    Prop :=
  (∃ firstAction secondAction,
    0 < source.weight firstAction secondAction ∧
    let coalition := repairedResidualPreferredCoalition
      owner remaining first second fixed firstAction secondAction
    source.remainingWrongSignNumerator reward / source.denominator ≤
        repairedResidualPreferredMargin reward owner remaining first second
          fixed firstAction secondAction ∧
      0 < source.remainingWrongSignNumerator reward / source.denominator ∧
      HasRepairedRemainingToggleResidual reward remaining coalition) ∨
  ∃ firstAction secondAction,
    0 < source.weight firstAction secondAction ∧
    let coalition := repairedResidualWithoutOwner owner remaining first second
      fixed firstAction secondAction
    (coalition.Nonempty ∧
        source.ownerFloorNumerator reward / source.denominator ≤
          quittingSetReward reward coalition owner -
            quittingSetReward reward (insert owner coalition) owner ∧
        0 < source.ownerFloorNumerator reward / source.denominator ∧
        HasRepairedOwnerToggleResidual reward owner coalition) ∨
      EmptyPunishmentPremiumToggleResidual reward owner

/-- A failed first retained sign reaches an actual selected repaired source and
then one of the checked deterministic-cell toggle residues. -/
def HasFirstFailureRepairedFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner second paid first : ι) (secondQuits : Bool) : Prop :=
  ∃ source : RepairedResidualPureExitSource owner second paid first secondQuits,
    HasRepairedPureExitFiniteResidual reward source

/-- Exact source-to-cell compiler for a failed first retained sign.  The
binary selection used to obtain the actual Nash root is reused, rather than
replaced by an unrelated repaired source. -/
theorem QuittingTerminalExploitabilityWitness.hasFirstFailureRepairedFiniteResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (hfailure : if firstQuits then
        purePaidDeletedFirstDifference reward owner first second secondQuits < 0
      else
        0 < purePaidDeletedFirstDifference reward owner first second
          secondQuits) :
    HasFirstFailureRepairedFiniteResidual reward owner second paid first
      secondQuits := by
  let background := quittingPureSetRoot
    (purePaidDeletedCoalition owner first second firstQuits secondQuits)
  obtain ⟨hjoinOld, hswitchCleared, hswitchPresent⟩ :=
    source.firstFailure_paidSignFailure_sourceSigns hfailure
  obtain ⟨selection, hresidual⟩ :=
    witness.exists_paidSignFailure_residual background owner paid first second
      firstQuits secondQuits source.paid_ne_owner.symm source.owner_ne_first
      source.owner_ne_second source.paid_ne_first source.paid_ne_second
      source.first_ne_second (by
        intro who
        rcases source.exhaust who with hpaid | howner | hfirst | hsecond
        · exact Or.inr (Or.inl hpaid)
        · exact Or.inl howner
        · exact Or.inr (Or.inr (Or.inl hfirst))
        · exact Or.inr (Or.inr (Or.inr hsecond)))
      (by simp [background, purePaidDeletedCoalition, purePaidRetainedSet,
        quittingPureSetRoot, quittingSetAction])
      (by
        cases firstQuits <;> cases secondQuits <;>
          simp [background, purePaidDeletedCoalition, purePaidRetainedSet,
            quittingPureSetRoot, quittingSetAction,
            source.owner_ne_second.symm, source.first_ne_second.symm])
      γ source.gamma_pos hjoinOld hswitchCleared hswitchPresent
  let repaired := source.firstFailureRepairedSource selection hjoinOld
    hswitchCleared
  refine ⟨repaired, ?_⟩
  have hremaining := source.firstFailure_remainingNumerator_eq selection
    hjoinOld hswitchCleared
  have howner := source.firstFailure_ownerFloorNumerator_eq selection
    hjoinOld hswitchCleared
  dsimp only at hresidual hremaining howner
  rcases hresidual with hremainingPos | hremainingNeg | hownerPos
  · left
    rcases hremainingPos with ⟨hfixed, hpositive⟩
    subst secondQuits
    apply witness.repairedWrongSignResidual repaired
    simpa [repaired, RepairedResidualPureExitSource.remainingWrongSignNumerator]
      using hremaining ▸ hpositive
  · left
    rcases hremainingNeg with ⟨hfixed, hnegative⟩
    subst secondQuits
    apply witness.repairedWrongSignResidual repaired
    have : repaired.remainingNumerator reward < 0 := hremaining ▸ hnegative
    simpa [repaired, RepairedResidualPureExitSource.remainingWrongSignNumerator]
      using (neg_pos.mpr this)
  · right
    apply witness.repairedOwnerFloorResidual_withoutEmpty hcard repaired
    exact howner ▸ hownerPos

/-- The two concrete large-base endpoint rows are exactly the payoff rows in
the pure-paid source. -/
theorem quittingLargeBaseRows_eq_purePaidRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid owner first second : ι)
    (hpaidOwner : paid ≠ owner) (hpaidFirst : paid ≠ first)
    (hpaidSecond : paid ≠ second) (hownerFirst : owner ≠ first)
    (hownerSecond : owner ≠ second) (hfirstSecond : first ≠ second) :
    (quittingLargeBaseFirstRow reward {paid, owner} {first, second} first second =
        fun action ↦
          quittingSetReward reward
              (purePaidOriginalCoalition paid owner first second true action)
              first -
            quittingSetReward reward
              (purePaidOriginalCoalition paid owner first second false action)
              first) ∧
      (quittingLargeBaseSecondRow reward {paid, owner} {first, second} first second =
        fun action ↦
          quittingSetReward reward
              (purePaidOriginalCoalition paid owner first second action true)
              second -
            quittingSetReward reward
              (purePaidOriginalCoalition paid owner first second action false)
              second) := by
  constructor
  · funext action
    have hinsert :
        insert first
            (purePaidOriginalCoalition paid owner first second false action) =
          purePaidOriginalCoalition paid owner first second true action := by
      rw [purePaidOriginalCoalition_eq_insert,
        purePaidOriginalCoalition_eq_insert,
        Finset.insert_comm first paid,
        insert_first_purePaidDeletedCoalition hownerFirst hfirstSecond]
    have herase :
        (purePaidOriginalCoalition paid owner first second false action).erase
            first =
          purePaidOriginalCoalition paid owner first second false action := by
      rw [purePaidOriginalCoalition_eq_insert,
        Finset.erase_insert_of_ne hpaidFirst,
        erase_first_purePaidDeletedCoalition hownerFirst hfirstSecond]
    rw [quittingLargeBaseFirstRow,
      ← quittingRootEndpointDifference_update_self reward 0 _ first
        (PMF.pure false)]
    rw [Function.update_comm hfirstSecond.symm,
      quittingLargeBasePureRoot_eq_purePaidOriginal paid owner first second
        hpaidOwner hpaidFirst hpaidSecond hownerFirst hownerSecond
        hfirstSecond false action]
    rw [quittingRootEndpointDifference_pureSet_of_erase_nonempty]
    · rw [hinsert, herase]
    · refine ⟨owner, Finset.mem_erase.mpr ⟨hownerFirst, ?_⟩⟩
      simp [purePaidOriginalCoalition, purePaidDeletedCoalition]
  · funext action
    have hinsert :
        insert second
            (purePaidOriginalCoalition paid owner first second action false) =
          purePaidOriginalCoalition paid owner first second action true := by
      rw [purePaidOriginalCoalition_eq_insert,
        purePaidOriginalCoalition_eq_insert,
        Finset.insert_comm second paid,
        insert_second_purePaidDeletedCoalition hownerSecond hfirstSecond]
    have herase :
        (purePaidOriginalCoalition paid owner first second action false).erase
            second =
          purePaidOriginalCoalition paid owner first second action false := by
      rw [purePaidOriginalCoalition_eq_insert,
        Finset.erase_insert_of_ne hpaidSecond,
        erase_second_purePaidDeletedCoalition hownerSecond hfirstSecond]
    rw [quittingLargeBaseSecondRow,
      ← quittingRootEndpointDifference_update_self reward 0 _ second
        (PMF.pure false),
      quittingLargeBasePureRoot_eq_purePaidOriginal paid owner first second
        hpaidOwner hpaidFirst hpaidSecond hownerFirst hownerSecond
        hfirstSecond action false]
    rw [quittingRootEndpointDifference_pureSet_of_erase_nonempty]
    · rw [hinsert, herase]
    · refine ⟨owner, Finset.mem_erase.mpr ⟨hownerSecond, ?_⟩⟩
      simp [purePaidOriginalCoalition, purePaidDeletedCoalition]

/-- A paid large-base pure cell is exactly the literal leave premium used by
the pure-paid source. -/
theorem quittingLargeBaseLeaveCell_eq_purePaidLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid owner first second : ι)
    (hpaidOwner : paid ≠ owner) (hpaidFirst : paid ≠ first)
    (hpaidSecond : paid ≠ second) (hownerFirst : owner ≠ first)
    (hownerSecond : owner ≠ second) (hfirstSecond : first ≠ second)
    (firstAction secondAction : Bool) :
    quittingLargeBaseLeaveCell reward {paid, owner} {first, second}
        first second paid firstAction secondAction =
      quittingSetReward reward
          (purePaidDeletedCoalition owner first second
            firstAction secondAction) paid -
        quittingSetReward reward
          (purePaidOriginalCoalition paid owner first second
            firstAction secondAction) paid := by
  let root := Function.update
    (Function.update
      (quittingLargeBaseReferenceRoot {paid, owner} {first, second} first)
      first (PMF.pure firstAction)) second (PMF.pure secondAction)
  have horiginal : root = quittingPureSetRoot
      (purePaidOriginalCoalition paid owner first second
        firstAction secondAction) :=
    quittingLargeBasePureRoot_eq_purePaidOriginal paid owner first second
      hpaidOwner hpaidFirst hpaidSecond hownerFirst hownerSecond hfirstSecond
      firstAction secondAction
  have hdeleted : Function.update root paid (PMF.pure false) =
      quittingPureSetRoot
        (purePaidDeletedCoalition owner first second
          firstAction secondAction) := by
    rw [horiginal, purePaidOriginalCoalition_eq_insert,
      update_quittingPureSetRoot_false,
      Finset.erase_insert (paid_not_mem_purePaidDeletedCoalition hpaidOwner
        hpaidFirst hpaidSecond firstAction secondAction)]
  have hendpoint := quittingRootEndpointDifference_update_self
    reward 0 root paid (PMF.pure false)
  rw [hdeleted, quittingRootEndpointDifference_purePaidDeleted_paid reward
    hpaidOwner hpaidFirst hpaidSecond firstAction secondAction] at hendpoint
  change -quittingRootEndpointDifference reward 0 root paid = _
  linarith

/-- The paid-pure arm of the actual finite dispatch carries all provenance
required by the source-native pure-paid deletion analysis. -/
theorem exists_purePaidBaseLeaveSource_of_actual_paidPure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseFirst baseSecond first second : ι)
    (hbaseNe : baseFirst ≠ baseSecond) (hfreeNe : first ≠ second)
    (hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      ({first, second} : Finset ι))
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (paidCell : HasPaidPureBinaryCell gamma
      (quittingLargeBaseFirstRow reward {baseFirst, baseSecond}
        {first, second} first second)
      (quittingLargeBaseSecondRow reward {baseFirst, baseSecond}
        {first, second} first second)
      (quittingLargeBaseLeaveObservable reward {baseFirst, baseSecond}
        {first, second} baseFirst baseSecond first second)) :
    ∃ paid owner firstAction secondAction,
      ((paid = baseFirst ∧ owner = baseSecond) ∨
        (paid = baseSecond ∧ owner = baseFirst)) ∧
      PurePaidBaseLeaveSource reward paid owner first second
        firstAction secondAction gamma := by
  obtain ⟨firstAction, secondAction, ownerIndex, hnash, hpaid⟩ := paidCell
  have hbaseFirstFirst : baseFirst ≠ first := by
    intro equality
    exact Finset.disjoint_left.mp hdisjoint
      (show baseFirst ∈ ({baseFirst, baseSecond} : Finset ι) by simp)
      (by simp [← equality])
  have hbaseFirstSecond : baseFirst ≠ second := by
    intro equality
    exact Finset.disjoint_left.mp hdisjoint
      (show baseFirst ∈ ({baseFirst, baseSecond} : Finset ι) by simp)
      (by simp [← equality])
  have hbaseSecondFirst : baseSecond ≠ first := by
    intro equality
    exact Finset.disjoint_left.mp hdisjoint
      (show baseSecond ∈ ({baseFirst, baseSecond} : Finset ι) by simp)
      (by simp [← equality])
  have hbaseSecondSecond : baseSecond ≠ second := by
    intro equality
    exact Finset.disjoint_left.mp hdisjoint
      (show baseSecond ∈ ({baseFirst, baseSecond} : Finset ι) by simp)
      (by simp [← equality])
  have hrows := quittingLargeBaseRows_eq_purePaidRows reward
    baseFirst baseSecond first second hbaseNe hbaseFirstFirst
      hbaseFirstSecond hbaseSecondFirst hbaseSecondSecond hfreeNe
  fin_cases ownerIndex
  · refine ⟨baseFirst, baseSecond, firstAction, secondAction,
      Or.inl ⟨rfl, rfl⟩, ?_⟩
    refine {
      paid_ne_owner := hbaseNe
      paid_ne_first := hbaseFirstFirst
      paid_ne_second := hbaseFirstSecond
      owner_ne_first := hbaseSecondFirst
      owner_ne_second := hbaseSecondSecond
      first_ne_second := hfreeNe
      exhaust := hexhaust
      originalPureNash := ?_
      gamma_pos := hgamma
      paidLeave := ?_ }
    · rw [← hrows.1, ← hrows.2]
      exact hnash
    · simpa [quittingLargeBaseLeaveObservable,
        quittingLargeBaseLeaveCell_eq_purePaidLeave reward baseFirst baseSecond
          first second hbaseNe hbaseFirstFirst hbaseFirstSecond
          hbaseSecondFirst hbaseSecondSecond hfreeNe] using hpaid
  · refine ⟨baseSecond, baseFirst, firstAction, secondAction,
      Or.inr ⟨rfl, rfl⟩, ?_⟩
    refine {
      paid_ne_owner := hbaseNe.symm
      paid_ne_first := hbaseSecondFirst
      paid_ne_second := hbaseSecondSecond
      owner_ne_first := hbaseFirstFirst
      owner_ne_second := hbaseFirstSecond
      first_ne_second := hfreeNe
      exhaust := ?_
      originalPureNash := ?_
      gamma_pos := hgamma
      paidLeave := ?_ }
    · intro who
      rcases hexhaust who with hfirstBase | hsecondBase | hfirst | hsecond
      · exact Or.inr (Or.inl hfirstBase)
      · exact Or.inl hsecondBase
      · exact Or.inr (Or.inr (Or.inl hfirst))
      · exact Or.inr (Or.inr (Or.inr hsecond))
    · have hrows' := quittingLargeBaseRows_eq_purePaidRows reward
        baseSecond baseFirst first second hbaseNe.symm hbaseSecondFirst
          hbaseSecondSecond hbaseFirstFirst hbaseFirstSecond hfreeNe
      rw [show ({baseSecond, baseFirst} : Finset ι) =
          {baseFirst, baseSecond} by ext who; simp [or_comm]] at hrows'
      rw [← hrows'.1, ← hrows'.2]
      exact hnash
    · have hleave := quittingLargeBaseLeaveCell_eq_purePaidLeave reward
        baseSecond baseFirst first second hbaseNe.symm hbaseSecondFirst
          hbaseSecondSecond hbaseFirstFirst hbaseFirstSecond hfreeNe
          firstAction secondAction
      rw [show ({baseSecond, baseFirst} : Finset ι) =
          {baseFirst, baseSecond} by ext who; simp [or_comm]] at hleave
      rw [← hleave]
      simpa [quittingLargeBaseLeaveObservable] using hpaid

/-- Exact obstruction left when a paid mixed cell cannot pass the checked
same-rate singleton-base deletion compiler. -/
def HasActualPaidMixedDeletionResidual
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
      0 < binaryClearedObservable alpha beta
        (quittingLargeBaseDeletedOwnerFloorCell reward owner free first second))

/-- In terminal-counterexample semantics, the mixed arm has a literal
nonzero reprojection residual or a positive punishment-priced owner floor. -/
theorem QuittingTerminalExploitabilityWitness.hasActualPaidMixedDeletionResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (baseFirst baseSecond first second : ι)
    (hbaseNe : baseFirst ≠ baseSecond) (hfreeNe : first ≠ second)
    (hdisjoint : Disjoint ({baseFirst, baseSecond} : Finset ι)
      ({first, second} : Finset ι))
    (hexhaust : ∀ who, who = baseFirst ∨ who = baseSecond ∨
      who = first ∨ who = second)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (mixed : HasPaidMixedBinaryCell gamma
      (quittingLargeBaseFirstRow reward {baseFirst, baseSecond}
        {first, second} first second)
      (quittingLargeBaseSecondRow reward {baseFirst, baseSecond}
        {first, second} first second)
      (quittingLargeBaseLeaveObservable reward {baseFirst, baseSecond}
        {first, second} baseFirst baseSecond first second)) :
    HasActualPaidMixedDeletionResidual reward baseFirst baseSecond first second
      gamma := by
  letI : Nonempty ι := ⟨baseFirst⟩
  let base : Finset ι := {baseFirst, baseSecond}
  let free : Finset ι := {first, second}
  let alpha := quittingLargeBaseFirstRow reward base free first second
  let beta := quittingLargeBaseSecondRow reward base free first second
  change IsStrictMatchingPenniesOrientation alpha beta ∧
      0 < binaryClearedDenominator alpha beta ∧
      ∃ ownerIndex,
        gamma * binaryClearedDenominator alpha beta ≤
          binaryClearedObservable alpha beta
            (quittingLargeBaseLeaveObservable reward base free
              baseFirst baseSecond first second ownerIndex) at mixed
  obtain ⟨horientation, _hdenominator, ownerIndex, hpaid⟩ := mixed
  have hfirst : first ∈ free := by simp [free]
  have hsecond : second ∈ free := by simp [free]
  have hfreeCover : ∀ who ∈ free, who = first ∨ who = second := by
    intro who hwho
    simpa [free] using hwho
  have cross (basePlayer : ι) (hbasePlayer : basePlayer ∈ base) :
      basePlayer ∉ free := by
    exact fun hfreePlayer ↦
      Finset.disjoint_left.mp hdisjoint (by simpa [base] using hbasePlayer)
        (by simpa [free] using hfreePlayer)
  fin_cases ownerIndex
  · refine ⟨baseFirst, baseSecond, Or.inl ⟨rfl, rfl⟩,
      horientation, ?_, ?_⟩
    · simpa [quittingLargeBaseLeaveObservable, base, free] using hpaid
    · by_contra hresidual
      push Not at hresidual
      have howner : baseSecond ∉ free := cross baseSecond (by simp [base])
      have hpaidNotFree : baseFirst ∉ free := cross baseFirst (by simp [base])
      have hplayerCover : ∀ who, who ∉ ({baseSecond} : Finset ι) ∪ free →
          who = baseFirst := by
        intro who houtside
        rcases hexhaust who with hfirstBase | hsecondBase | hfirstWho | hsecondWho
        · exact hfirstBase
        · subst who
          exact False.elim (houtside (by simp))
        · subst who
          exact False.elim (houtside (by simp [free]))
        · subst who
          exact False.elim (houtside (by simp [free]))
      have huniform := exists_uniformPayoff_of_largeBase_mixedDeletion_of_clearedData
        reward baseSecond baseFirst free howner hpaidNotFree hbaseNe.symm
          hfirst hsecond hfreeNe hfreeCover hplayerCover gamma hgamma alpha beta
          horientation hresidual.1 hresidual.2.1 hresidual.2.2
          (by
            rw [show ({baseSecond, baseFirst} : Finset ι) =
              {baseFirst, baseSecond} by ext who; simp [or_comm]]
            simpa [quittingLargeBaseLeaveObservable, base, free] using hpaid)
      exact witness.not_exists_uniformEquilibriumPayoff huniform
  · refine ⟨baseSecond, baseFirst, Or.inr ⟨rfl, rfl⟩,
      horientation, ?_, ?_⟩
    · simpa [quittingLargeBaseLeaveObservable, base, free] using hpaid
    · by_contra hresidual
      push Not at hresidual
      have howner : baseFirst ∉ free := cross baseFirst (by simp [base])
      have hpaidNotFree : baseSecond ∉ free := cross baseSecond (by simp [base])
      have hplayerCover : ∀ who, who ∉ ({baseFirst} : Finset ι) ∪ free →
          who = baseSecond := by
        intro who houtside
        rcases hexhaust who with hfirstBase | hsecondBase | hfirstWho | hsecondWho
        · subst who
          exact False.elim (houtside (by simp))
        · exact hsecondBase
        · subst who
          exact False.elim (houtside (by simp [free]))
        · subst who
          exact False.elim (houtside (by simp [free]))
      have huniform := exists_uniformPayoff_of_largeBase_mixedDeletion_of_clearedData
        reward baseFirst baseSecond free howner hpaidNotFree hbaseNe
          hfirst hsecond hfreeNe hfreeCover hplayerCover gamma hgamma alpha beta
          horientation hresidual.1 hresidual.2.1 hresidual.2.2
          (by simpa [quittingLargeBaseLeaveObservable, base, free] using hpaid)
      exact witness.not_exists_uniformEquilibriumPayoff huniform

/-- The pure arm after all currently checked source-native descents.  Failed
retained signs carry an actual repaired four-cell source.  A positive owner
floor is already reduced to a nonempty membership residue or, at the empty
cell, to the card-four nonowner-toggle residue. -/
def HasPurePaidChainFiniteResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (paid owner first second : ι) (firstQuits secondQuits : Bool) : Prop :=
  ((if firstQuits then
      purePaidDeletedFirstDifference reward owner first second secondQuits < 0
    else
      0 < purePaidDeletedFirstDifference reward owner first second secondQuits) ∧
    HasFirstFailureRepairedFiniteResidual reward owner second paid first
      secondQuits) ∨
  ((if secondQuits then
      purePaidDeletedSecondDifference reward owner first second firstQuits < 0
    else
      0 < purePaidDeletedSecondDifference reward owner first second firstQuits) ∧
    HasFirstFailureRepairedFiniteResidual reward owner first paid second
      firstQuits) ∨
  (0 < purePaidOwnerFloorExcess reward owner first second
      firstQuits secondQuits ∧
    (((purePaidRetainedSet first second firstQuits secondQuits).Nonempty ∧
        HasPurePaidSureExitResidual reward paid first second
          firstQuits secondQuits) ∨
      EmptyPunishmentPremiumToggleResidual reward owner))

/-- A source-native pure-paid cell in a four-player terminal counterexample
lands in the finite residual above; the empty punishment branch is removed. -/
theorem QuittingTerminalExploitabilityWitness.hasPurePaidChainFiniteResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card ι = 4)
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ) :
    HasPurePaidChainFiniteResidual reward paid owner first second
      firstQuits secondQuits := by
  rcases witness.hasPurePaidSingletonResidual source with
    hfirst | hsecond | hfloor
  · exact Or.inl ⟨hfirst,
      witness.hasFirstFailureRepairedFiniteResidual hcard source hfirst⟩
  · exact Or.inr (Or.inl ⟨hsecond,
      witness.hasFirstFailureRepairedFiniteResidual hcard source.swapFree
        (by
          simpa [purePaidDeletedFirstDifference,
            purePaidDeletedSecondDifference,
            purePaidDeletedCoalition_swap] using hsecond)⟩)
  · right
    right
    refine ⟨hfloor, ?_⟩
    by_cases hretained :
        (purePaidRetainedSet first second firstQuits secondQuits).Nonempty
    · exact Or.inl ⟨hretained,
        witness.hasPurePaidSureExitResidual source hretained hfloor⟩
    · right
      have hretainedEmpty :
          purePaidRetainedSet first second firstQuits secondQuits = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hretained
      have hpremium : quittingSoloReward reward owner owner <
          quittingPunishmentValue reward owner := by
        change reward ⟨{owner}, Finset.singleton_nonempty owner⟩ owner <
          quittingPunishmentValue reward owner
        simpa [purePaidOwnerFloorExcess, hretained, hretainedEmpty,
          purePaidDeletedCoalition,
          quittingSoloReward] using hfloor
      exact (witness.emptyPunishmentPremium_residual hcard owner hpremium).2.2

/-- Exact terminal-counterexample output of the actual support-two large-base
finite dispatch.  The pure arm reaches repaired sources or literal toggles;
the mixed arm retains only the three deletion obstructions. -/
def HasSupportTwoPaidChainResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseFirst baseSecond first second : ι) (gamma : ℝ) : Prop :=
  (∃ paid owner firstAction secondAction,
    ((paid = baseFirst ∧ owner = baseSecond) ∨
      (paid = baseSecond ∧ owner = baseFirst)) ∧
    HasPurePaidChainFiniteResidual reward paid owner first second
      firstAction secondAction) ∨
  HasActualPaidMixedDeletionResidual reward baseFirst baseSecond first second gamma

/-- Positive support-two large-base gap, under an actual terminal witness,
contracts to the checked pure-chain or mixed-deletion finite residue. -/
theorem QuittingTerminalExploitabilityWitness.hasSupportTwoPaidChainResidual
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
    HasSupportTwoPaidChainResidual reward baseFirst baseSecond first second
      gamma := by
  rcases paidPure_or_paidMixed_of_actual_largeBase_gap_labels reward
      {baseFirst, baseSecond} {first, second} baseFirst baseSecond first second
      hfreeNe rfl rfl hdisjoint hexhaust gamma hgamma gap with hpure | hmixed
  · left
    obtain ⟨paid, owner, firstAction, secondAction, hpair, source⟩ :=
      exists_purePaidBaseLeaveSource_of_actual_paidPure reward
        baseFirst baseSecond first second hbaseNe hfreeNe hdisjoint hexhaust
          gamma hgamma hpure
    exact ⟨paid, owner, firstAction, secondAction, hpair,
      witness.hasPurePaidChainFiniteResidual hcard source⟩
  · exact Or.inr (witness.hasActualPaidMixedDeletionResidual
      baseFirst baseSecond first second hbaseNe hfreeNe hdisjoint hexhaust
        gamma hgamma hmixed)

end GameTheory
