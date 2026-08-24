/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.FiniteWeightedSelection
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PaidSignFailureBinaryReequilibration
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PurePaidBaseLeaveDescent

/-!
# Repaired-residual pure-exit descent

Positive cleared residuals of a supplied four-cell repaired root contain a
positive-weight deterministic cell with the same normalized margin. At that
cell, the responsible label is quantitatively stable in its preferred pure
membership action. The remaining finite test is exactly a sure-exit set or a
strict membership toggle by a different label.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Explicit four-cell weighted sum. -/
def repairedFourCellWeightedSum (weight score : Bool → Bool → ℝ) : ℝ :=
  weight false false * score false false +
    weight true false * score true false +
    weight false true * score false true +
    weight true true * score true true

/-- Cleared weighted selection on the four Boolean cells. -/
theorem exists_bool_cell_weight_pos_and_total_mul_score_ge
    (weight score : Bool → Bool → ℝ) (total weighted : ℝ)
    (weight_nonneg : ∀ first second, 0 ≤ weight first second)
    (sum_weight : repairedFourCellWeightedSum weight (fun _ _ ↦ 1) = total)
    (weighted_eq : repairedFourCellWeightedSum weight score = weighted)
    (total_pos : 0 < total) :
    ∃ first second, 0 < weight first second ∧
      weighted ≤ total * score first second := by
  let pairWeight : Bool × Bool → ℝ := fun cell => weight cell.1 cell.2
  let pairScore : Bool × Bool → ℝ := fun cell => score cell.1 cell.2
  have hnonneg : ∀ cell, 0 ≤ pairWeight cell := fun cell =>
    weight_nonneg cell.1 cell.2
  have hsum : ∑ cell, pairWeight cell = total := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool]
    dsimp [pairWeight]
    rw [← sum_weight]
    simp [repairedFourCellWeightedSum]
    ring
  have hweighted : ∑ cell, pairWeight cell * pairScore cell = weighted := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool,
      Fintype.sum_bool, Fintype.sum_bool]
    dsimp [pairWeight, pairScore]
    rw [← weighted_eq]
    simp [repairedFourCellWeightedSum]
    ring
  obtain ⟨cell, hweight, hbound⟩ :=
    MathUE.exists_weight_pos_and_total_mul_score_ge
      pairWeight pairScore total weighted hnonneg hsum hweighted total_pos
  exact ⟨cell.1, cell.2, hweight, hbound⟩

/-- Four arbitrary, distinct labels exhausting the ambient player type. -/
structure RepairedResidualFourLabels
    (owner remaining first second : ι) : Prop where
  owner_ne_remaining : owner ≠ remaining
  owner_ne_first : owner ≠ first
  owner_ne_second : owner ≠ second
  remaining_ne_first : remaining ≠ first
  remaining_ne_second : remaining ≠ second
  first_ne_second : first ≠ second
  exhaust : ∀ who,
    who = owner ∨ who = remaining ∨ who = first ∨ who = second

/-- Deterministic terminal coalition in one repaired Boolean cell. -/
def repairedResidualCellCoalition
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    Finset ι :=
  insert owner <|
    (if fixed then {remaining} else ∅) ∪
      (if firstAction then {first} else ∅) ∪
        if secondAction then {second} else ∅

/-- The cell with the fixed remaining label removed. -/
def repairedResidualWithoutRemaining
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    Finset ι :=
  (repairedResidualCellCoalition owner remaining first second
    fixed firstAction secondAction).erase remaining

/-- The cell with the sure owner removed. -/
def repairedResidualWithoutOwner
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    Finset ι :=
  (repairedResidualCellCoalition owner remaining first second
    fixed firstAction secondAction).erase owner

/-- Fixed remaining-label Quit-minus-Continue difference in one cell. -/
def repairedResidualRemainingDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) : ℝ :=
  let without := repairedResidualWithoutRemaining owner remaining first second
    fixed firstAction secondAction
  quittingSetReward reward (insert remaining without) remaining -
    quittingSetReward reward without remaining

/-- Exact punishment-priced Continue-minus-Quit excess of the sure owner in
one cell. -/
def repairedResidualOwnerFloorExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) : ℝ :=
  let without := repairedResidualWithoutOwner owner remaining first second
    fixed firstAction secondAction
  if without.Nonempty then
    quittingSetReward reward without owner -
      quittingSetReward reward (insert owner without) owner
  else
    quittingPunishmentValue reward owner -
      quittingSetReward reward (insert owner without) owner

/-- Cleared four-cell data of a repaired residual. -/
structure RepairedResidualPureExitSource
    (owner remaining first second : ι) (fixed : Bool) where
  labels : RepairedResidualFourLabels owner remaining first second
  weight : Bool → Bool → ℝ
  denominator : ℝ
  weight_nonneg : ∀ firstAction secondAction,
    0 ≤ weight firstAction secondAction
  sum_weight : repairedFourCellWeightedSum weight (fun _ _ ↦ 1) = denominator
  denominator_pos : 0 < denominator

/-- The division-free binary re-equilibration weights supply exactly the
four-cell source used by the repaired-residual descent. -/
def RepairedResidualPureExitSource.ofPaidSignSelection
    {join switch : Bool → ℝ}
    (selection : PaidSignFailureBinarySelection join switch)
    (oldAction : Bool)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hjoinOld : join false ≤ -gamma)
    (hswitchCleared : 0 < switch false)
    {owner remaining first second : ι} {fixed : Bool}
    (labels : RepairedResidualFourLabels owner remaining first second) :
    RepairedResidualPureExitSource owner remaining first second fixed where
  labels := labels
  weight := fun firstAction secondAction ↦
    selection.weight firstAction (Bool.xor oldAction secondAction)
  denominator := selection.denominator
  weight_nonneg := fun firstAction secondAction ↦
    selection.weight_nonneg hgamma hjoinOld hswitchCleared firstAction
      (Bool.xor oldAction secondAction)
  sum_weight := by
    have hsum := selection.sum_weight
    cases oldAction <;>
      simp [repairedFourCellWeightedSum,
        PaidSignFailureBinarySelection.weightedSum] at hsum ⊢ <;> linarith
  denominator_pos := selection.denominator_pos hgamma hjoinOld hswitchCleared

/-- A failed first retained sign in the actual pure-paid packet produces the
four-cell repaired-residual source, with the retained player's switch bit
converted to its literal Quit action. -/
theorem PurePaidBaseLeaveSource.exists_repairedResidualSource_of_firstFailure
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (hfailure : if firstQuits then
        purePaidDeletedFirstDifference reward owner first second secondQuits < 0
      else
        0 < purePaidDeletedFirstDifference reward owner first second
          secondQuits) :
    Nonempty
      (RepairedResidualPureExitSource owner second paid first secondQuits) := by
  let background := quittingPureSetRoot
    (purePaidDeletedCoalition owner first second firstQuits secondQuits)
  obtain ⟨hjoinOld, hswitchCleared, hswitchPresent⟩ :=
    source.firstFailure_paidSignFailure_sourceSigns hfailure
  obtain ⟨selection⟩ :=
    PaidSignFailureBinarySelection.exists_of_sourceSigns source.gamma_pos
      hjoinOld hswitchCleared hswitchPresent
  refine ⟨RepairedResidualPureExitSource.ofPaidSignSelection selection
    firstQuits source.gamma_pos hjoinOld hswitchCleared ?_⟩
  refine {
    owner_ne_remaining := source.owner_ne_second
    owner_ne_first := source.paid_ne_owner.symm
    owner_ne_second := source.owner_ne_first
    remaining_ne_first := source.paid_ne_second.symm
    remaining_ne_second := source.first_ne_second.symm
    first_ne_second := source.paid_ne_first
    exhaust := ?_ }
  intro who
  rcases source.exhaust who with hpaid | howner | hfirst | hsecond
  · exact Or.inr (Or.inr (Or.inl hpaid))
  · exact Or.inl howner
  · exact Or.inr (Or.inr (Or.inr hfirst))
  · exact Or.inr (Or.inl hsecond)

/-- Symmetric source-native repaired residual when the second retained sign
fails. -/
theorem PurePaidBaseLeaveSource.exists_repairedResidualSource_of_secondFailure
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {paid owner first second : ι} {firstQuits secondQuits : Bool} {γ : ℝ}
    (source : PurePaidBaseLeaveSource reward paid owner first second
      firstQuits secondQuits γ)
    (hfailure : if secondQuits then
        purePaidDeletedSecondDifference reward owner first second firstQuits < 0
      else
        0 < purePaidDeletedSecondDifference reward owner first second
          firstQuits) :
    Nonempty
      (RepairedResidualPureExitSource owner first paid second firstQuits) := by
  apply source.swapFree.exists_repairedResidualSource_of_firstFailure
  simpa [purePaidDeletedFirstDifference, purePaidDeletedSecondDifference,
    purePaidDeletedCoalition_swap] using hfailure

/-- Cleared aggregate owner-floor residual. -/
def RepairedResidualPureExitSource.ownerFloorNumerator
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  repairedFourCellWeightedSum source.weight fun firstAction secondAction =>
    repairedResidualOwnerFloorExcess reward owner remaining first second
      fixed firstAction secondAction

/-- Cleared aggregate remaining-label endpoint difference. -/
def RepairedResidualPureExitSource.remainingNumerator
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  repairedFourCellWeightedSum source.weight fun firstAction secondAction =>
    repairedResidualRemainingDifference reward owner remaining first second
      fixed firstAction secondAction

/-- The remaining label's endpoint defect in its fixed-action orientation. -/
def RepairedResidualPureExitSource.remainingWrongSignNumerator
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  if fixed then -source.remainingNumerator reward
  else source.remainingNumerator reward

/-- Cellwise remaining-label defect in the orientation of its fixed action. -/
def repairedResidualRemainingWrongSign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) : ℝ :=
  if fixed then
    -repairedResidualRemainingDifference reward owner remaining first second
      fixed firstAction secondAction
  else
    repairedResidualRemainingDifference reward owner remaining first second
      fixed firstAction secondAction

/-- Preferred coalition after flipping the wrong fixed action. -/
def repairedResidualPreferredCoalition
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    Finset ι :=
  let without := repairedResidualWithoutRemaining owner remaining first second
    fixed firstAction secondAction
  if fixed then without else insert remaining without

omit [Fintype ι] in
@[simp] theorem owner_mem_repairedResidualCellCoalition
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    owner ∈ repairedResidualCellCoalition owner remaining first second
      fixed firstAction secondAction := by
  simp [repairedResidualCellCoalition]

omit [Fintype ι] in
theorem remaining_mem_repairedResidualCellCoalition_iff
    {owner remaining first second : ι}
    (labels : RepairedResidualFourLabels owner remaining first second)
    (fixed firstAction secondAction : Bool) :
    remaining ∈ repairedResidualCellCoalition owner remaining first second
      fixed firstAction secondAction ↔ fixed = true := by
  cases fixed <;> cases firstAction <;> cases secondAction <;>
    simp [repairedResidualCellCoalition, labels.owner_ne_remaining.symm,
      labels.remaining_ne_first, labels.remaining_ne_second]

omit [Fintype ι] in
theorem owner_not_mem_repairedResidualWithoutOwner
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    owner ∉ repairedResidualWithoutOwner owner remaining first second
      fixed firstAction secondAction := by
  simp [repairedResidualWithoutOwner]

omit [Fintype ι] in
theorem insert_owner_repairedResidualWithoutOwner
    {owner remaining first second : ι}
    (fixed firstAction secondAction : Bool) :
    insert owner (repairedResidualWithoutOwner owner remaining first second
      fixed firstAction secondAction) =
      repairedResidualCellCoalition owner remaining first second
        fixed firstAction secondAction := by
  rw [repairedResidualWithoutOwner]
  exact Finset.insert_erase
    (owner_mem_repairedResidualCellCoalition owner remaining first second
      fixed firstAction secondAction)

omit [Fintype ι] in
theorem remaining_not_mem_repairedResidualWithoutRemaining
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    remaining ∉ repairedResidualWithoutRemaining owner remaining first second
      fixed firstAction secondAction := by
  simp [repairedResidualWithoutRemaining]

omit [Fintype ι] in
theorem owner_mem_repairedResidualWithoutRemaining
    {owner remaining first second : ι}
    (labels : RepairedResidualFourLabels owner remaining first second)
    (fixed firstAction secondAction : Bool) :
    owner ∈ repairedResidualWithoutRemaining owner remaining first second
      fixed firstAction secondAction := by
  exact Finset.mem_erase.mpr ⟨labels.owner_ne_remaining,
    owner_mem_repairedResidualCellCoalition owner remaining first second
      fixed firstAction secondAction⟩

omit [Fintype ι] in
theorem repairedResidualPreferredCoalition_nonempty
    {owner remaining first second : ι}
    (labels : RepairedResidualFourLabels owner remaining first second)
    (fixed firstAction secondAction : Bool) :
    (repairedResidualPreferredCoalition owner remaining first second
      fixed firstAction secondAction).Nonempty := by
  refine ⟨owner, ?_⟩
  cases fixed <;>
    simp [repairedResidualPreferredCoalition,
      owner_mem_repairedResidualWithoutRemaining labels]

omit [Fintype ι] in
theorem repairedResidualPreferredCoalition_remaining_membership
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    remaining ∈ repairedResidualPreferredCoalition owner remaining first second
      fixed firstAction secondAction ↔ fixed = false := by
  cases fixed <;>
    simp [repairedResidualPreferredCoalition,
      remaining_not_mem_repairedResidualWithoutRemaining]

/-- The cleared owner residual selects a positive-weight cell with the same
normalized owner-floor margin. -/
theorem RepairedResidualPureExitSource.exists_ownerFloor_cell
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (positive : 0 < source.ownerFloorNumerator reward) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      source.ownerFloorNumerator reward / source.denominator ≤
        repairedResidualOwnerFloorExcess reward owner remaining first second
          fixed firstAction secondAction ∧
      0 < repairedResidualOwnerFloorExcess reward owner remaining first second
        fixed firstAction secondAction := by
  obtain ⟨firstAction, secondAction, hweight, hbound⟩ :=
    exists_bool_cell_weight_pos_and_total_mul_score_ge
      source.weight
      (fun firstAction secondAction =>
        repairedResidualOwnerFloorExcess reward owner remaining first second
          fixed firstAction secondAction)
      source.denominator (source.ownerFloorNumerator reward)
      source.weight_nonneg source.sum_weight rfl source.denominator_pos
  have hnormalized : source.ownerFloorNumerator reward / source.denominator ≤
      repairedResidualOwnerFloorExcess reward owner remaining first second
        fixed firstAction secondAction := by
    apply (div_le_iff₀ source.denominator_pos).2
    rwa [mul_comm]
  have hnormalizedPos : 0 <
      source.ownerFloorNumerator reward / source.denominator :=
    div_pos positive source.denominator_pos
  exact ⟨firstAction, secondAction, hweight, hnormalized,
    hnormalizedPos.trans_le hnormalized⟩

omit [Fintype ι] in
/-- The wrong remaining-label aggregate selects a positive-weight cell with
the same normalized oriented endpoint margin. -/
theorem RepairedResidualPureExitSource.exists_wrongSign_cell
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (positive : 0 < source.remainingWrongSignNumerator reward) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      source.remainingWrongSignNumerator reward / source.denominator ≤
        repairedResidualRemainingWrongSign reward owner remaining first second
          fixed firstAction secondAction ∧
      0 < repairedResidualRemainingWrongSign reward owner remaining first second
        fixed firstAction secondAction := by
  have hweighted : repairedFourCellWeightedSum source.weight
      (fun firstAction secondAction =>
        repairedResidualRemainingWrongSign reward owner remaining first second
          fixed firstAction secondAction) =
      source.remainingWrongSignNumerator reward := by
    cases fixed
    · simp [repairedResidualRemainingWrongSign,
        RepairedResidualPureExitSource.remainingWrongSignNumerator,
        RepairedResidualPureExitSource.remainingNumerator,
        repairedFourCellWeightedSum]
    · simp [repairedResidualRemainingWrongSign,
        RepairedResidualPureExitSource.remainingWrongSignNumerator,
        RepairedResidualPureExitSource.remainingNumerator,
        repairedFourCellWeightedSum]
      ring
  obtain ⟨firstAction, secondAction, hweight, hbound⟩ :=
    exists_bool_cell_weight_pos_and_total_mul_score_ge
      source.weight
      (fun firstAction secondAction =>
        repairedResidualRemainingWrongSign reward owner remaining first second
          fixed firstAction secondAction)
      source.denominator (source.remainingWrongSignNumerator reward)
      source.weight_nonneg source.sum_weight hweighted source.denominator_pos
  have hnormalized :
      source.remainingWrongSignNumerator reward / source.denominator ≤
        repairedResidualRemainingWrongSign reward owner remaining first second
          fixed firstAction secondAction := by
    apply (div_le_iff₀ source.denominator_pos).2
    rwa [mul_comm]
  have hnormalizedPos : 0 <
      source.remainingWrongSignNumerator reward / source.denominator :=
    div_pos positive source.denominator_pos
  exact ⟨firstAction, secondAction, hweight, hnormalized,
    hnormalizedPos.trans_le hnormalized⟩

/-- Quantitative stability margin of the remaining label at its preferred
post-toggle coalition. -/
def repairedResidualPreferredMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) : ℝ :=
  let preferred := repairedResidualPreferredCoalition owner remaining first second
    fixed firstAction secondAction
  if fixed then
    quittingSetReward reward preferred remaining -
      quittingSetReward reward (insert remaining preferred) remaining
  else
    quittingSetReward reward preferred remaining -
      quittingSetReward reward (preferred.erase remaining) remaining

omit [Fintype ι] in
theorem repairedResidualPreferredMargin_eq_wrongSign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner remaining first second : ι) (fixed firstAction secondAction : Bool) :
    repairedResidualPreferredMargin reward owner remaining first second
        fixed firstAction secondAction =
      repairedResidualRemainingWrongSign reward owner remaining first second
        fixed firstAction secondAction := by
  have hnotMem := remaining_not_mem_repairedResidualWithoutRemaining
    owner remaining first second fixed firstAction secondAction
  cases fixed
  · simp [repairedResidualPreferredMargin,
      repairedResidualPreferredCoalition,
      repairedResidualRemainingWrongSign,
      repairedResidualRemainingDifference, hnotMem]
  · simp [repairedResidualPreferredMargin,
      repairedResidualPreferredCoalition,
      repairedResidualRemainingWrongSign,
      repairedResidualRemainingDifference]

/-- Strict toggle residual after excluding the quantitatively stable owner. -/
def HasRepairedOwnerToggleResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (coalition : Finset ι) : Prop :=
  (∃ who ∈ coalition,
    quittingSetReward reward coalition who <
      quittingSetReward reward (coalition.erase who) who) ∨
    ∃ who ∉ insert owner coalition,
      quittingSetReward reward coalition who <
        quittingSetReward reward (insert who coalition) who

/-- Strict toggle residual after excluding the quantitatively stable
remaining label. -/
def HasRepairedRemainingToggleResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (remaining : ι) (coalition : Finset ι) : Prop :=
  (∃ who ∈ coalition, who ≠ remaining ∧
    quittingSetReward reward coalition who <
      quittingSetReward reward (coalition.erase who) who) ∨
    ∃ who ∉ coalition, who ≠ remaining ∧
      quittingSetReward reward coalition who <
        quittingSetReward reward (insert who coalition) who

/-- Positive owner-floor aggregate: a selected cell is either the exact empty
punishment premium, a checked sure-exit payoff, or a nonempty coalition with
the owner quantitatively stable and a strict toggle elsewhere. -/
theorem RepairedResidualPureExitSource.ownerFloor_descent
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (positive : 0 < source.ownerFloorNumerator reward) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      let coalition := repairedResidualWithoutOwner owner remaining first second
        fixed firstAction secondAction
      (coalition = ∅ ∧
          source.ownerFloorNumerator reward / source.denominator ≤
            quittingPunishmentValue reward owner -
              quittingSoloReward reward owner owner ∧
          0 < source.ownerFloorNumerator reward / source.denominator) ∨
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (quittingSetReward reward coalition) ∨
        (coalition.Nonempty ∧
          source.ownerFloorNumerator reward / source.denominator ≤
            quittingSetReward reward coalition owner -
              quittingSetReward reward (insert owner coalition) owner ∧
          0 < source.ownerFloorNumerator reward / source.denominator ∧
          HasRepairedOwnerToggleResidual reward owner coalition) := by
  obtain ⟨firstAction, secondAction, hweight, hmargin, hcellPos⟩ :=
    source.exists_ownerFloor_cell reward positive
  refine ⟨firstAction, secondAction, hweight, ?_⟩
  let coalition := repairedResidualWithoutOwner owner remaining first second
    fixed firstAction secondAction
  by_cases hcoalition : coalition.Nonempty
  · have hcellEq :
        repairedResidualOwnerFloorExcess reward owner remaining first second
            fixed firstAction secondAction =
          quittingSetReward reward coalition owner -
            quittingSetReward reward (insert owner coalition) owner := by
      simp [repairedResidualOwnerFloorExcess, coalition, hcoalition]
    have hstable : quittingSetReward reward (insert owner coalition) owner <
        quittingSetReward reward coalition owner := by
      rw [hcellEq] at hcellPos
      linarith
    by_cases hsure : IsQuittingSureExitSet reward coalition
    · exact Or.inr (Or.inl
        (isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
          reward hsure))
    · right
      right
      refine ⟨hcoalition, ?_, div_pos positive source.denominator_pos, ?_⟩
      · rwa [hcellEq] at hmargin
      · unfold HasRepairedOwnerToggleResidual
        by_cases hmember : ∀ who ∈ coalition,
            quittingSetReward reward (coalition.erase who) who ≤
              quittingSetReward reward coalition who
        · have houtsider : ¬ ∀ who ∉ coalition,
              quittingSetReward reward (insert who coalition) who ≤
                quittingSetReward reward coalition who := by
            intro houtsider
            exact hsure ⟨hmember, houtsider⟩
          push Not at houtsider
          obtain ⟨who, hwho, hstrict⟩ := houtsider
          have hne : who ≠ owner := by
            intro heq
            subst who
            exact (not_lt_of_ge hstable.le) hstrict
          refine Or.inr ⟨who, ?_, hstrict⟩
          simpa only [Finset.mem_insert, not_or] using And.intro hne hwho
        · push Not at hmember
          obtain ⟨who, hwho, hstrict⟩ := hmember
          exact Or.inl ⟨who, hwho, hstrict⟩
  · have hempty : coalition = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcoalition
    left
    refine ⟨hempty, ?_, div_pos positive source.denominator_pos⟩
    have hcellEq :
        repairedResidualOwnerFloorExcess reward owner remaining first second
            fixed firstAction secondAction =
          quittingPunishmentValue reward owner -
            quittingSoloReward reward owner owner := by
      unfold repairedResidualOwnerFloorExcess
      change (if coalition.Nonempty then _ else _) = _
      rw [if_neg hcoalition]
      change quittingPunishmentValue reward owner -
        quittingSetReward reward (insert owner coalition) owner = _
      rw [hempty]
      simp only [Finset.insert_empty]
      rw [quittingSetReward_singleton_eq_soloReward]
    rwa [hcellEq] at hmargin

/-- Wrong remaining-label aggregate: a selected preferred-action coalition
is either a checked sure-exit payoff or has the remaining label
quantitatively stable and a strict toggle by a different label. -/
theorem RepairedResidualPureExitSource.wrongSign_descent
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (positive : 0 < source.remainingWrongSignNumerator reward) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      let coalition := repairedResidualPreferredCoalition
        owner remaining first second fixed firstAction secondAction
      (quittingGame reward).IsUniformEquilibriumPayoff none
          (quittingSetReward reward coalition) ∨
        (source.remainingWrongSignNumerator reward / source.denominator ≤
            repairedResidualPreferredMargin reward owner remaining first second
              fixed firstAction secondAction ∧
          0 < source.remainingWrongSignNumerator reward / source.denominator ∧
          HasRepairedRemainingToggleResidual reward remaining coalition) := by
  obtain ⟨firstAction, secondAction, hweight, hmargin, hcellPos⟩ :=
    source.exists_wrongSign_cell reward positive
  refine ⟨firstAction, secondAction, hweight, ?_⟩
  let coalition := repairedResidualPreferredCoalition
    owner remaining first second fixed firstAction secondAction
  have hcoalition : coalition.Nonempty :=
    repairedResidualPreferredCoalition_nonempty source.labels
      fixed firstAction secondAction
  have hmarginPreferred :
      source.remainingWrongSignNumerator reward / source.denominator ≤
        repairedResidualPreferredMargin reward owner remaining first second
          fixed firstAction secondAction := by
    rwa [repairedResidualPreferredMargin_eq_wrongSign]
  have hnormalizedPos :
      0 < source.remainingWrongSignNumerator reward / source.denominator :=
    div_pos positive source.denominator_pos
  have hstable :
      (fixed = false ∧ remaining ∈ coalition ∧
        quittingSetReward reward (coalition.erase remaining) remaining <
          quittingSetReward reward coalition remaining) ∨
      (fixed = true ∧ remaining ∉ coalition ∧
        quittingSetReward reward (insert remaining coalition) remaining <
          quittingSetReward reward coalition remaining) := by
    cases fixed
    · left
      refine ⟨rfl, ?_, ?_⟩
      · exact (repairedResidualPreferredCoalition_remaining_membership
          owner remaining first second false firstAction secondAction).2 rfl
      · rw [← repairedResidualPreferredMargin_eq_wrongSign] at hcellPos
        simpa [repairedResidualPreferredMargin, coalition] using hcellPos
    · right
      refine ⟨rfl, ?_, ?_⟩
      · exact fun hmem =>
          by simpa using
            ((repairedResidualPreferredCoalition_remaining_membership
              owner remaining first second true firstAction secondAction).1 hmem)
      · rw [← repairedResidualPreferredMargin_eq_wrongSign] at hcellPos
        simpa [repairedResidualPreferredMargin, coalition] using hcellPos
  by_cases hsure : IsQuittingSureExitSet reward coalition
  · exact Or.inl
      (isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
        reward hsure)
  · right
    refine ⟨hmarginPreferred, hnormalizedPos, ?_⟩
    unfold HasRepairedRemainingToggleResidual
    by_cases hmember : ∀ who ∈ coalition,
        quittingSetReward reward (coalition.erase who) who ≤
          quittingSetReward reward coalition who
    · have houtsider : ¬ ∀ who ∉ coalition,
          quittingSetReward reward (insert who coalition) who ≤
            quittingSetReward reward coalition who := by
        intro houtsider
        exact hsure ⟨hmember, houtsider⟩
      push Not at houtsider
      obtain ⟨who, hwho, hstrict⟩ := houtsider
      have hne : who ≠ remaining := by
        intro heq
        subst who
        rcases hstable with hmemberStable | houtStable
        · exact hwho hmemberStable.2.1
        · exact (not_lt_of_ge houtStable.2.2.le) hstrict
      exact Or.inr ⟨who, hwho, hne, hstrict⟩
    · push Not at hmember
      obtain ⟨who, hwho, hstrict⟩ := hmember
      have hne : who ≠ remaining := by
        intro heq
        subst who
        rcases hstable with hmemberStable | houtStable
        · exact (not_lt_of_ge hmemberStable.2.2.le) hstrict
        · exact houtStable.2.1 hwho
      exact Or.inl ⟨who, hwho, hne, hstrict⟩

/-- Terminal-witness form of the owner descent, with the sure-exit branch
removed and only the empty premium or strict nonowner toggle retained. -/
theorem QuittingTerminalExploitabilityWitness.repairedOwnerFloorResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (positive : 0 < source.ownerFloorNumerator reward) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      let coalition := repairedResidualWithoutOwner owner remaining first second
        fixed firstAction secondAction
      (coalition = ∅ ∧
          source.ownerFloorNumerator reward / source.denominator ≤
            quittingPunishmentValue reward owner -
              quittingSoloReward reward owner owner ∧
          0 < source.ownerFloorNumerator reward / source.denominator) ∨
        (coalition.Nonempty ∧
          source.ownerFloorNumerator reward / source.denominator ≤
            quittingSetReward reward coalition owner -
              quittingSetReward reward (insert owner coalition) owner ∧
          0 < source.ownerFloorNumerator reward / source.denominator ∧
          HasRepairedOwnerToggleResidual reward owner coalition) := by
  obtain ⟨firstAction, secondAction, hweight, result⟩ :=
    source.ownerFloor_descent reward positive
  refine ⟨firstAction, secondAction, hweight, ?_⟩
  rcases result with hempty | huniform | hresidual
  · exact Or.inl hempty
  · exact False.elim (witness.not_exists_uniformEquilibriumPayoff
      ⟨_, huniform⟩)
  · exact Or.inr hresidual

/-- Terminal-witness form of the wrong-label descent: the selected preferred
coalition has a quantitative remaining-label margin and a strict toggle by a
different player. -/
theorem QuittingTerminalExploitabilityWitness.repairedWrongSignResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {owner remaining first second : ι} {fixed : Bool}
    (source : RepairedResidualPureExitSource owner remaining first second fixed)
    (positive : 0 < source.remainingWrongSignNumerator reward) :
    ∃ firstAction secondAction,
      0 < source.weight firstAction secondAction ∧
      let coalition := repairedResidualPreferredCoalition
        owner remaining first second fixed firstAction secondAction
      source.remainingWrongSignNumerator reward / source.denominator ≤
          repairedResidualPreferredMargin reward owner remaining first second
            fixed firstAction secondAction ∧
        0 < source.remainingWrongSignNumerator reward / source.denominator ∧
        HasRepairedRemainingToggleResidual reward remaining coalition := by
  obtain ⟨firstAction, secondAction, hweight, result⟩ :=
    source.wrongSign_descent reward positive
  refine ⟨firstAction, secondAction, hweight, ?_⟩
  rcases result with huniform | hresidual
  · exact False.elim (witness.not_exists_uniformEquilibriumPayoff
      ⟨_, huniform⟩)
  · exact hresidual

end GameTheory
