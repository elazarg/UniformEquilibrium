import UniformEquilibrium.Quitting.Examples.CrossedMatchingFixture
import UniformEquilibrium.Quitting.Classification.BlockDeletion
import UniformEquilibrium.Quitting.Classification.QuietExtension.PureAbsorbingChildDebtObstruction
import UniformEquilibrium.Quitting.Root.StationaryTailSplice
import UniformEquilibrium.Quitting.Stationary.JointNeverMass

/-! # Literal unsafe child witnesses of the crossed-matching table

Every proper nonempty child has a chosen exact absorbing terminal Nash
profile with a profitable omitted player. This does not assert that every
equilibrium of a child has a profitable quiet lift.
-/

noncomputable section

namespace GameTheory.CrossedMatchingFixture

open QuittingSureSetOwnerRepair
open scoped BigOperators

def childSet (row : Fin 14) : Finset (Fin 4) :=
  Math.Finset.finFourCoalitionOfRow row.castSucc

def childExitSet (row : Fin 14) : Finset (Fin 4) :=
  match row.val with
  | 0 => {0}
  | 1 => {1}
  | 2 => {0}
  | 3 => {2}
  | 4 => {0, 2}
  | 5 => {1}
  | 6 => {1}
  | 7 => {3}
  | 8 => {0}
  | 9 => {1, 3}
  | 10 => {0}
  | 11 => {2}
  | 12 => {3}
  | _ => {2}

def childOutside (row : Fin 14) : Fin 4 :=
  (![2, 3, 2, 0, 1, 3, 3, 1, 2, 2, 2, 0, 1, 0] : Fin 14 → Fin 4) row

def childGain (row : Fin 14) : ℝ :=
  (![177 / 32, 113 / 14, 177 / 32, 177 / 32, 1 / 2, 113 / 14, 113 / 14,
    113 / 14, 177 / 32, 1 / 2, 177 / 32, 177 / 32, 113 / 14, 177 / 32]
      : Fin 14 → ℝ) row

theorem childSet_complete (selected : Finset (Fin 4))
    (hnonempty : selected.Nonempty) (hproper : selected ≠ Finset.univ) :
    ∃ row : Fin 14, childSet row = selected := by
  exact Math.Finset.finFour_properNonemptyCoalition_row selected hnonempty hproper

theorem childExit_nonempty (row : Fin 14) : (childExitSet row).Nonempty := by
  fin_cases row <;> simp [childExitSet]

theorem childExit_subset (row : Fin 14) : childExitSet row ⊆ childSet row := by
  fin_cases row <;> decide

theorem childOutside_not_mem (row : Fin 14) : childOutside row ∉ childSet row := by
  fin_cases row <;> decide

theorem child_insertion_and_withdrawal (row : Fin 14) (player : Fin 4)
    (hplayer : player ∈ childSet row) :
    quittingSetReward reward ((childExitSet row).erase player) player ≤
        quittingSetReward reward (childExitSet row) player ∧
      quittingSetReward reward (insert player (childExitSet row)) player ≤
        quittingSetReward reward (childExitSet row) player := by
  fin_cases row <;> fin_cases player
  all_goals norm_num [childSet, Math.Finset.finFourCoalitionOfRow] at hplayer
  all_goals norm_num +decide [childExitSet, quittingSetReward, reward,
    Math.FiniteCoalition.binaryCode_finFour]

theorem childOutside_gain_eq (row : Fin 14) :
    quittingSetReward reward (insert (childOutside row) (childExitSet row))
        (childOutside row) -
      quittingSetReward reward (childExitSet row) (childOutside row) = childGain row := by
  fin_cases row <;>
    norm_num +decide [childOutside, childExitSet, childGain, quittingSetReward, reward,
      Math.FiniteCoalition.binaryCode_finFour]

theorem childGain_positive (row : Fin 14) : 0 < childGain row := by
  fin_cases row <;> norm_num [childGain]

abbrev Child (row : Fin 14) := QuittingBlockSurvivor (childSet row)ᶜ

def childActive (row : Fin 14) : Finset (Child row) :=
  (childExitSet row).subtype (fun player => player ∉ (childSet row)ᶜ)

theorem childActive_map (row : Fin 14) :
    (childActive row).map (Function.Embedding.subtype
      (p := fun player : Fin 4 => player ∉ (childSet row)ᶜ)) = childExitSet row := by
  exact Finset.subtype_map_of_mem (fun player hplayer =>
    by simpa using childExit_subset row hplayer)

theorem childActive_nonempty (row : Fin 14) : (childActive row).Nonempty := by
  apply Finset.map_nonempty.mp
  rw [childActive_map]
  exact childExit_nonempty row

def childReward (row : Fin 14) := quittingDeleteBlockReward reward (childSet row)ᶜ

def childProfile (row : Fin 14) : (quittingGame (childReward row)).BehaviorProfile :=
  quittingStationaryProfile (childReward row) (quittingPureSetRoot (childActive row))

theorem child_terminalNash (row : Fin 14) :
    (quittingGame (childReward row)).IsεAsymptoticNash
      (quittingTerminalPayoff (childReward row)) 0 (childProfile row) := by
  apply (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet _ _).mpr
  apply (isQuittingSureExitSet_deleteBlockReward_iff reward (childSet row)ᶜ _).mpr
  rw [childActive_map]
  constructor
  · intro player hplayer
    exact (child_insertion_and_withdrawal row player
      (childExit_subset row hplayer)).1
  · intro player hplayer _
    exact (child_insertion_and_withdrawal row player (by simpa using hplayer)).2

theorem child_jointNever_eq_zero (row : Fin 14) :
    (∏ player, (quittingBehaviorStoppingLaw (childReward row)
      (childProfile row player) none).toReal) = 0 := by
  apply prod_stoppingLaw_none_stationary_eq_zero
  rw [stationaryContinueMass_pureSetRoot_of_nonempty (childActive_nonempty row)]
  norm_num

theorem quiet_childProfile_eq (row : Fin 14) :
    quittingLiftDeletedProfile reward (fun player => player ∈ (childSet row)ᶜ)
        (childProfile row) =
      quittingStationaryProfile reward (quittingPureSetRoot (childExitSet row)) := by
  unfold childProfile childReward
  rw [quittingLiftDeletedProfile_stationary_pureSetRoot, childActive_map]

/-- The literal Quit-now gain of the chosen omitted player. -/
theorem quiet_childOutside_gain_eq (row : Fin 14) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingLiftDeletedProfile reward (fun player => player ∈ (childSet row)ᶜ)
            (childProfile row))
          (childOutside row) (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0)))
        (childOutside row) -
      quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward (fun player => player ∈ (childSet row)ᶜ)
          (childProfile row)) (childOutside row) = childGain row := by
  rw [quiet_childProfile_eq, quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_pureSetRoot, childOutside_gain_eq]

/-- No finite weighted child-debt and Never charge controls this actual outsider gain. -/
theorem quiet_gain_gt_weighted_childDebt_add_never (row : Fin 14)
    (weight : Child row → ℝ) (neverCoefficient : ℝ) :
    (∑ player, weight player *
      (quittingBehaviorDeviationPayoffCap (childReward row) (childProfile row) player -
        quittingTerminalPayoff (childReward row) (childProfile row) player)) +
      neverCoefficient * (∏ player, (quittingBehaviorStoppingLaw (childReward row)
        (childProfile row player) none).toReal) < childGain row := by
  have houtside : childOutside row ∈ (childSet row)ᶜ := by
    simpa using childOutside_not_mem row
  have hgain : 0 < quittingTerminalPayoff reward
      (Function.update
        (quittingLiftDeletedProfile reward (fun player => player ∈ (childSet row)ᶜ)
          (childProfile row))
        (childOutside row) (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0)))
      (childOutside row) -
    quittingTerminalPayoff reward
      (quittingLiftDeletedProfile reward (fun player => player ∈ (childSet row)ᶜ)
        (childProfile row)) (childOutside row) := by
    rw [quiet_childOutside_gain_eq]
    exact childGain_positive row
  have hbound := quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child reward
    (fun player => player ∈ (childSet row)ᶜ) (childProfile row)
    (child_terminalNash row) (child_jointNever_eq_zero row) ⟨childOutside row, houtside⟩
    (quittingPureTimeBehaviorStrategy reward (childOutside row) (some 0)) hgain
    weight neverCoefficient
  change (∑ player, weight player *
      (quittingBehaviorDeviationPayoffCap (childReward row) (childProfile row) player -
        quittingTerminalPayoff (childReward row) (childProfile row) player)) +
    neverCoefficient * (∏ player, (quittingBehaviorStoppingLaw (childReward row)
      (childProfile row player) none).toReal) < _ at hbound
  rw [quiet_childOutside_gain_eq] at hbound
  exact hbound

/-- Exhaustive coverage of proper nonempty children, with one unsafe witness per child. -/
theorem exists_unsafe_witness_for_every_proper_child (selected : Finset (Fin 4))
    (hnonempty : selected.Nonempty) (hproper : selected ≠ Finset.univ) :
    ∃ row : Fin 14, childSet row = selected ∧
      (quittingGame (childReward row)).IsεAsymptoticNash
        (quittingTerminalPayoff (childReward row)) 0 (childProfile row) ∧
      (∏ player, (quittingBehaviorStoppingLaw (childReward row)
        (childProfile row player) none).toReal) = 0 ∧
      ∀ (weight : Child row → ℝ) (neverCoefficient : ℝ),
        (∑ player, weight player *
          (quittingBehaviorDeviationPayoffCap (childReward row) (childProfile row) player -
            quittingTerminalPayoff (childReward row) (childProfile row) player)) +
          neverCoefficient * (∏ player, (quittingBehaviorStoppingLaw (childReward row)
            (childProfile row player) none).toReal) < childGain row := by
  obtain ⟨row, hrow⟩ := childSet_complete selected hnonempty hproper
  exact ⟨row, hrow, child_terminalNash row, child_jointNever_eq_zero row,
    quiet_gain_gt_weighted_childDebt_add_never row⟩

end GameTheory.CrossedMatchingFixture
