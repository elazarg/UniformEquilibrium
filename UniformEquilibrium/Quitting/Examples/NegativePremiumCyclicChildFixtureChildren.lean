import MathUE.Finset.FinFourNonemptyCoalitions
import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixtures
import UniformEquilibrium.Quitting.Classification.BlockDeletion
import UniformEquilibrium.Quitting.Classification.BlockDeletionInequality
import UniformEquilibrium.Quitting.Classification.QuietExtension.PureAbsorbingChildDebtObstruction
import UniformEquilibrium.Quitting.Stationary.JointNeverMass
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinFixedTarget
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderDebt

/-! # Actual unsafe child witnesses for the negative-premium fixture

All fourteen nonempty proper carriers have exact full-behavior child Nash
profiles, zero joint Never, and positive outside gains after the literal quiet
lift. Thirteen use pure exits; `{1,2,3}` uses a dedicated child-only cycle.
No assertion is made that every equilibrium of a child has an unsafe lift.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures.Children

open QuittingSureSetOwnerRepair
open scoped BigOperators

def childSet (row : Fin 14) : Finset Player :=
  Math.Finset.finFourCoalitionOfRow row.castSucc

def pureExit (row : Fin 13) : Finset Player :=
  match row.val with
  | 0 => {0}
  | 1 => {1}
  | 2 => {1}
  | 3 => {2}
  | 4 => {2}
  | 5 => {1}
  | 6 => {1}
  | 7 => {3}
  | 8 => {0, 3}
  | 9 => {3}
  | 10 => {0, 3}
  | 11 => {2}
  | _ => {2}

def pureOutside (row : Fin 13) : Player :=
  (![1, 3, 3, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1] : Fin 13 → Player) row

theorem childSet_covers_all_proper (selected : Finset Player)
    (hnonempty : selected.Nonempty) (hproper : selected ≠ Finset.univ) :
    ∃ row : Fin 14, childSet row = selected :=
  Math.Finset.finFour_properNonemptyCoalition_row selected hnonempty hproper

theorem pureExit_nonempty (row : Fin 13) : (pureExit row).Nonempty := by
  fin_cases row <;> simp [pureExit]

theorem pureExit_subset (row : Fin 13) : pureExit row ⊆ childSet row.castSucc := by
  fin_cases row <;> decide

theorem pureOutside_not_mem (row : Fin 13) : pureOutside row ∉ childSet row.castSucc := by
  fin_cases row <;> decide

theorem pure_insertion_and_withdrawal (row : Fin 13) (player : Player)
    (hplayer : player ∈ childSet row.castSucc) :
    quittingSetReward survivorReward ((pureExit row).erase player) player ≤
        quittingSetReward survivorReward (pureExit row) player ∧
      quittingSetReward survivorReward (insert player (pureExit row)) player ≤
        quittingSetReward survivorReward (pureExit row) player := by
  fin_cases row <;> fin_cases player
  all_goals
    norm_num [childSet, Math.Finset.finFourCoalitionOfRow] at hplayer
  all_goals
    norm_num [pureExit, quittingSetReward, survivorReward, lower, upper,
      Finset.ext_iff, Fin.forall_fin_succ]

theorem pureOutside_gain_eq (row : Fin 13) :
    quittingSetReward survivorReward (insert (pureOutside row) (pureExit row))
        (pureOutside row) -
      quittingSetReward survivorReward (pureExit row) (pureOutside row) =
        if row = 0 then 1 - loss else if row = 8 ∨ row = 10 then 2 - loss else 1 := by
  fin_cases row <;>
    norm_num [pureOutside, pureExit, quittingSetReward, survivorReward, lower, upper, loss,
      Finset.ext_iff, Fin.forall_fin_succ]

theorem pureOutside_gain_pos (row : Fin 13) :
    0 < quittingSetReward survivorReward (insert (pureOutside row) (pureExit row))
        (pureOutside row) -
      quittingSetReward survivorReward (pureExit row) (pureOutside row) := by
  rw [pureOutside_gain_eq]
  split_ifs <;> norm_num [loss]

abbrev PureChild (row : Fin 13) := QuittingBlockSurvivor (childSet row.castSucc)ᶜ

def pureActive (row : Fin 13) : Finset (PureChild row) :=
  (pureExit row).subtype (fun player => player ∉ (childSet row.castSucc)ᶜ)

theorem pureActive_map (row : Fin 13) :
    (pureActive row).map (Function.Embedding.subtype
      (p := fun player : Player => player ∉ (childSet row.castSucc)ᶜ)) = pureExit row := by
  apply Finset.subtype_map_of_mem
  intro player hplayer
  simpa using pureExit_subset row hplayer

theorem pureActive_nonempty (row : Fin 13) : (pureActive row).Nonempty := by
  apply Finset.map_nonempty.mp
  rw [pureActive_map]
  exact pureExit_nonempty row

def pureChildReward (row : Fin 13) :=
  quittingDeleteBlockReward survivorReward (childSet row.castSucc)ᶜ

def pureChildProfile (row : Fin 13) :
    (quittingGame (pureChildReward row)).BehaviorProfile :=
  quittingStationaryProfile (pureChildReward row) (quittingPureSetRoot (pureActive row))

theorem pureChild_terminalNash (row : Fin 13) :
    (quittingGame (pureChildReward row)).IsεAsymptoticNash
      (quittingTerminalPayoff (pureChildReward row)) 0 (pureChildProfile row) := by
  apply (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet _ _).mpr
  apply (isQuittingSureExitSet_deleteBlockReward_iff
    survivorReward (childSet row.castSucc)ᶜ _).mpr
  rw [pureActive_map]
  constructor
  · intro player hplayer
    exact (pure_insertion_and_withdrawal row player (pureExit_subset row hplayer)).1
  · intro player hplayer _
    exact (pure_insertion_and_withdrawal row player (by simpa using hplayer)).2

theorem pureChild_jointNever_eq_zero (row : Fin 13) :
    (∏ player, (quittingBehaviorStoppingLaw (pureChildReward row)
      (pureChildProfile row player) none).toReal) = 0 := by
  apply prod_stoppingLaw_none_stationary_eq_zero
  rw [stationaryContinueMass_pureSetRoot_of_nonempty (pureActive_nonempty row)]
  norm_num

def pureQuietLift (row : Fin 13) : (quittingGame survivorReward).BehaviorProfile :=
  quittingLiftDeletedProfile survivorReward (fun player => player ∈ (childSet row.castSucc)ᶜ)
    (pureChildProfile row)

theorem pureQuietLift_eq (row : Fin 13) :
    pureQuietLift row =
      quittingStationaryProfile survivorReward (quittingPureSetRoot (pureExit row)) := by
  unfold pureQuietLift pureChildProfile pureChildReward
  rw [quittingLiftDeletedProfile_stationary_pureSetRoot, pureActive_map]

theorem pureQuietLift_quitNow_gain_eq (row : Fin 13) :
    quittingTerminalPayoff survivorReward
        (Function.update (pureQuietLift row) (pureOutside row)
          (quittingPureTimeBehaviorStrategy survivorReward (pureOutside row) (some 0)))
        (pureOutside row) -
      quittingTerminalPayoff survivorReward (pureQuietLift row) (pureOutside row) =
        if row = 0 then 1 - loss else if row = 8 ∨ row = 10 then 2 - loss else 1 := by
  rw [pureQuietLift_eq, quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_pureSetRoot]
  exact pureOutside_gain_eq row

theorem pureQuietLift_gain_gt_all_weighted_debt (row : Fin 13)
    (weight : PureChild row → ℝ) (neverCoefficient : ℝ) :
    (∑ player, weight player *
      (quittingBehaviorDeviationPayoffCap (pureChildReward row) (pureChildProfile row) player -
        quittingTerminalPayoff (pureChildReward row) (pureChildProfile row) player)) +
      neverCoefficient * (∏ player, (quittingBehaviorStoppingLaw (pureChildReward row)
        (pureChildProfile row player) none).toReal) <
      quittingTerminalPayoff survivorReward
          (Function.update (pureQuietLift row) (pureOutside row)
            (quittingPureTimeBehaviorStrategy survivorReward (pureOutside row) (some 0)))
          (pureOutside row) -
        quittingTerminalPayoff survivorReward (pureQuietLift row) (pureOutside row) := by
  apply quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child
    survivorReward (fun player => player ∈ (childSet row.castSucc)ᶜ) (pureChildProfile row)
    (pureChild_terminalNash row) (pureChild_jointNever_eq_zero row)
    ⟨pureOutside row, by simpa using pureOutside_not_mem row⟩
    (quittingPureTimeBehaviorStrategy survivorReward (pureOutside row) (some 0))
    _ weight neverCoefficient
  change 0 < quittingTerminalPayoff survivorReward
      (Function.update (pureQuietLift row) (pureOutside row)
        (quittingPureTimeBehaviorStrategy survivorReward (pureOutside row) (some 0)))
      (pureOutside row) -
    quittingTerminalPayoff survivorReward (pureQuietLift row) (pureOutside row)
  rw [pureQuietLift_quitNow_gain_eq]
  split_ifs <;> norm_num [loss]

/-! ## The dedicated child-only cycle on `{1,2,3}` -/

abbrev CyclicChild := QuittingBlockSurvivor ({0} : Finset Player)

def cyclicChildReward := quittingDeleteBlockReward survivorReward ({0} : Finset Player)

def cyclicChildCycle (phase : Fin 3) (who : CyclicChild) : PMF Bool :=
  cycle highRates phase who.1

def cyclicChildValue (phase : Fin 3) (who : CyclicChild) : ℝ := highValue phase who.1

theorem cyclicChild_extend (phase : Fin 3) :
    quittingExtendDeletedRoot (fun player : Player => player ∈ ({0} : Finset Player))
      (cyclicChildCycle phase) = cycle highRates phase := by
  funext player
  by_cases hplayer : player = 0
  · subst player
    fin_cases phase <;>
      simp [cycle, jointRoot, soloOne, soloTwo, highRates, PairedCycle.root,
        quittingSoloStationaryRoot, quittingExtendDeletedRoot, quittingHazardCoin_zero]
  · exact quittingExtendDeletedRoot_apply
      (fun player : Player => player ∈ ({0} : Finset Player)) (cyclicChildCycle phase)
      ⟨player, by simpa using hplayer⟩

/-- Policy evaluation holds at every loss; no full-parent Nash claim is used. -/
theorem highCycle_policy (phase : Fin 3) :
    highValue phase = quittingRootSuccessorPayoff survivorReward
      (highValue (finRotate 3 phase)) (cycle highRates phase) := by
  fin_cases phase
  · change highValue 0 =
      quittingRootSuccessorPayoff survivorReward (highValue 1) (jointRoot highRates)
    rw [high_joint_eq_solo, quittingRootSuccessorPayoff_solo]
    funext who
    fin_cases who <;>
      norm_num [highValue, quittingSoloReward, survivorReward, quittingSingletonTerminal,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  · change highValue 1 =
      quittingRootSuccessorPayoff survivorReward (highValue 2) (soloOne highRates)
    rw [soloOne, quittingRootSuccessorPayoff_solo]
    funext who
    fin_cases who <;>
      norm_num [highValue, highRates, quittingSoloReward, survivorReward,
        quittingSingletonTerminal, quittingHazardCoin_true_toReal,
        quittingHazardCoin_false_toReal]
  · change highValue 2 =
      quittingRootSuccessorPayoff survivorReward (highValue 0) (soloTwo highRates)
    rw [soloTwo, quittingRootSuccessorPayoff_solo]
    funext who
    fin_cases who <;>
      norm_num [highValue, highRates, quittingSoloReward, survivorReward,
        quittingSingletonTerminal, quittingHazardCoin_true_toReal,
        quittingHazardCoin_false_toReal]

theorem cyclicChild_policy (phase : Fin 3) :
    cyclicChildValue phase = quittingRootSuccessorPayoff cyclicChildReward
      (cyclicChildValue (finRotate 3 phase)) (cyclicChildCycle phase) := by
  funext who
  change highValue phase who.1 = quittingRootExpectedPayoff
    (quittingDeleteReward survivorReward
      (fun player : Player => player ∈ ({0} : Finset Player)))
    (cyclicChildValue (finRotate 3 phase)) (cyclicChildCycle phase) who
  rw [← quittingRootExpectedPayoff_extendDeletedRoot_of_apply_eq survivorReward
    (fun player : Player => player ∈ ({0} : Finset Player))
    (highValue (finRotate 3 phase)) (cyclicChildValue (finRotate 3 phase))
    (cyclicChildCycle phase) who rfl, cyclicChild_extend]
  exact congrFun (highCycle_policy phase) who.1

theorem cyclicChild_updatedRootPayoff (phase : Fin 3) (who : CyclicChild)
    (marginal : PMF Bool) :
    quittingRootExpectedPayoff cyclicChildReward (cyclicChildValue (finRotate 3 phase))
        (Function.update (cyclicChildCycle phase) who marginal) who =
      quittingRootExpectedPayoff survivorReward (highValue (finRotate 3 phase))
        (Function.update (cycle highRates phase) who.1 marginal) who.1 := by
  rw [← cyclicChild_extend, Function.update_quittingExtendDeletedRoot]
  exact (quittingRootExpectedPayoff_extendDeletedRoot_of_apply_eq survivorReward
    (fun player : Player => player ∈ ({0} : Finset Player))
    (highValue (finRotate 3 phase)) (cyclicChildValue (finRotate 3 phase))
    (Function.update (cyclicChildCycle phase) who marginal) who rfl).symm

theorem cyclicChild_quit_le (phase : Fin 3) (who : CyclicChild) :
    quittingRootQuitPayoff survivorReward (highValue (finRotate 3 phase))
      (cycle highRates phase) who.1 ≤ highValue phase who.1 := by
  apply (quit_le loss survivorReward survivor_raw highRates _ phase who.1).trans
  rcases who with ⟨who, hwho⟩
  fin_cases phase <;> fin_cases who
  all_goals norm_num at hwho
  all_goals norm_num [quitUpper, highRates, highValue, loss]

theorem cyclicChild_rootNash (phase : Fin 3) :
    IsεQuittingRootNash cyclicChildReward (cyclicChildValue (finRotate 3 phase))
      0 (cyclicChildCycle phase) := by
  apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash _ _ _ _).mp
  apply (isεQuittingRootEndpointNash_iff_purePayoff_le _ _ _ _).mpr
  intro who
  rw [← cyclicChild_policy, add_zero]
  constructor
  · change quittingRootExpectedPayoff cyclicChildReward
      (cyclicChildValue (finRotate 3 phase))
      (Function.update (cyclicChildCycle phase) who (PMF.pure true)) who ≤ _
    rw [cyclicChild_updatedRootPayoff]
    exact cyclicChild_quit_le phase who
  · change quittingRootExpectedPayoff cyclicChildReward
      (cyclicChildValue (finRotate 3 phase))
      (Function.update (cyclicChildCycle phase) who (PMF.pure false)) who ≤ _
    rw [cyclicChild_updatedRootPayoff]
    exact (high_continue loss survivorReward survivor_raw phase who.1).le

theorem cyclicChild_opponentMass (phase : Fin 3) (who : CyclicChild) :
    quittingStationaryFixedOpponentsContinueMass (cyclicChildCycle phase) who =
      quittingStationaryFixedOpponentsContinueMass (cycle highRates phase) who.1 := by
  change quittingStationaryContinueMass
      (Function.update (cyclicChildCycle phase) who (PMF.pure false)) =
    quittingStationaryContinueMass
      (Function.update (cycle highRates phase) who.1 (PMF.pure false))
  rw [← quittingStationaryContinueMass_extendDeletedRoot ({0} : Finset Player),
    ← Function.update_quittingExtendDeletedRoot, cyclicChild_extend]

theorem cyclicChild_contracts (who : CyclicChild) :
    (∏ phase : Fin 3,
      quittingStationaryFixedOpponentsContinueMass (cyclicChildCycle phase) who) < 1 := by
  simp_rw [cyclicChild_opponentMass]
  exact cycle_contracts highRates who.1

def cyclicChildProfile : (quittingGame cyclicChildReward).BehaviorProfile :=
  quittingCyclicBehaviorProfile cyclicChildReward cyclicChildCycle 0

theorem cyclicChild_terminalNash :
    (quittingGame cyclicChildReward).IsεAsymptoticNash
      (quittingTerminalPayoff cyclicChildReward) 0 cyclicChildProfile :=
  isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate
    cyclicChildReward cyclicChildCycle cyclicChildValue 0
    cyclicChild_policy cyclicChild_rootNash cyclicChild_contracts

theorem cyclicChild_jointNever_eq_zero :
    (∏ who, (quittingBehaviorStoppingLaw cyclicChildReward
      (cyclicChildProfile who) none).toReal) = 0 := by
  rw [← quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
  let who : CyclicChild := ⟨1, by decide⟩
  have hopponent : Filter.Tendsto
      (quittingOpponentSurvivalWeight (quittingCyclicRootSequence cyclicChildCycle 0) who 0)
      Filter.atTop (nhds 0) :=
    tendsto_zero_quittingOpponentSurvivalWeight_cyclicRootSequence
      cyclicChildCycle 0 who (cyclicChild_contracts who)
  have hjoint : Filter.Tendsto
      (quittingJointSurvivalWeight (quittingCyclicRootSequence cyclicChildCycle 0) 0)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun fuel => quittingJointSurvivalWeight_nonneg _ _ fuel
    · exact fun fuel => quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        (quittingCyclicRootSequence cyclicChildCycle 0) who 0 fuel
    · exact hopponent
  change quittingLiveMassLimit cyclicChildReward
    (quittingCyclicBehaviorProfile cyclicChildReward cyclicChildCycle 0) = 0
  rw [quittingCyclicBehaviorProfile,
    quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
  exact tendsto_nhds_unique
    (tendsto_quittingJointSurvivalLimit (quittingCyclicRootSequence cyclicChildCycle 0) 0) hjoint

def cyclicQuietLift : (quittingGame survivorReward).BehaviorProfile :=
  quittingLiftDeletedProfile survivorReward
    (fun player : Player => player ∈ ({0} : Finset Player)) cyclicChildProfile

theorem cyclicQuietLift_eq :
    cyclicQuietLift = quittingCyclicBehaviorProfile survivorReward (cycle highRates) 0 := by
  unfold cyclicQuietLift quittingLiftDeletedProfile cyclicChildProfile cyclicChildReward
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile]
  unfold quittingInfinitePathProfile quittingCyclicBehaviorProfile
  congr 1
  funext time
  exact cyclicChild_extend (quittingCyclicOrbit 0 time)

theorem cyclicQuietLift_pivot_payoff :
    quittingTerminalPayoff survivorReward cyclicQuietLift 0 = 8 / 13 := by
  rw [cyclicQuietLift_eq, quittingTerminalPayoff_cyclicBehaviorProfile]
  rw [← eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff survivorReward
    (cycle highRates) highValue highCycle_policy (cycle_contracts highRates)]
  norm_num [highValue]

theorem cyclicQuietLift_pivot_quitNow_payoff :
    quittingTerminalPayoff survivorReward
      (Function.update cyclicQuietLift 0
        (quittingPureTimeBehaviorStrategy survivorReward 0 (some 0))) 0 =
      1 - 2 * loss / 3 := by
  rw [cyclicQuietLift_eq, quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_cyclicBehaviorProfile,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue survivorReward
    (quittingCyclicRootSequence (cycle highRates) 0) 0 (highValue 1) 0]
  rw [quittingCyclicRootSequence_zero]
  change quittingRootQuitPayoff survivorReward (highValue 1) (jointRoot highRates) 0 = _
  rw [joint_quit_zero loss survivorReward survivor_raw]
  norm_num [highRates]
  ring

theorem cyclicQuietLift_quitNow_gain_eq :
    quittingTerminalPayoff survivorReward
        (Function.update cyclicQuietLift 0
          (quittingPureTimeBehaviorStrategy survivorReward 0 (some 0))) 0 -
      quittingTerminalPayoff survivorReward cyclicQuietLift 0 = (15 - 26 * loss) / 39 := by
  rw [cyclicQuietLift_pivot_quitNow_payoff, cyclicQuietLift_pivot_payoff]
  ring

theorem cyclicQuietLift_gain_gt_all_weighted_debt
    (weight : CyclicChild → ℝ) (neverCoefficient : ℝ) :
    (∑ who, weight who *
      (quittingBehaviorDeviationPayoffCap cyclicChildReward cyclicChildProfile who -
        quittingTerminalPayoff cyclicChildReward cyclicChildProfile who)) +
      neverCoefficient * (∏ who, (quittingBehaviorStoppingLaw cyclicChildReward
        (cyclicChildProfile who) none).toReal) <
      quittingTerminalPayoff survivorReward
          (Function.update cyclicQuietLift 0
            (quittingPureTimeBehaviorStrategy survivorReward 0 (some 0))) 0 -
        quittingTerminalPayoff survivorReward cyclicQuietLift 0 := by
  apply quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child
    survivorReward (fun player : Player => player ∈ ({0} : Finset Player)) cyclicChildProfile
    cyclicChild_terminalNash cyclicChild_jointNever_eq_zero
    ⟨0, by decide⟩ (quittingPureTimeBehaviorStrategy survivorReward 0 (some 0))
    _ weight neverCoefficient
  change 0 < quittingTerminalPayoff survivorReward
      (Function.update cyclicQuietLift 0
        (quittingPureTimeBehaviorStrategy survivorReward 0 (some 0))) 0 -
    quittingTerminalPayoff survivorReward cyclicQuietLift 0
  rw [cyclicQuietLift_quitNow_gain_eq]
  norm_num [loss]

/-- Every actual proper carrier has a chosen exact child with an unsafe quiet lift.
This is a witness theorem, not a claim about all child equilibria. -/
theorem exists_unsafe_exact_child (selected : Finset Player)
    (hnonempty : selected.Nonempty) (hproper : selected ≠ Finset.univ) :
    ∃ (profile : (quittingGame
          (quittingDeleteBlockReward survivorReward selectedᶜ)).BehaviorProfile)
      (outside : {who : Player // who ∈ selectedᶜ}),
      (quittingGame (quittingDeleteBlockReward survivorReward selectedᶜ)).IsεAsymptoticNash
        (quittingTerminalPayoff (quittingDeleteBlockReward survivorReward selectedᶜ)) 0 profile ∧
      (∏ who, (quittingBehaviorStoppingLaw
        (quittingDeleteBlockReward survivorReward selectedᶜ) (profile who) none).toReal) = 0 ∧
      0 < quittingTerminalPayoff survivorReward
          (Function.update (quittingLiftDeletedProfile survivorReward
              (fun who => who ∈ selectedᶜ) profile) outside.1
            (quittingPureTimeBehaviorStrategy survivorReward outside.1 (some 0))) outside.1 -
        quittingTerminalPayoff survivorReward
          (quittingLiftDeletedProfile survivorReward (fun who => who ∈ selectedᶜ) profile)
          outside.1 := by
  obtain ⟨row, rfl⟩ := childSet_covers_all_proper selected hnonempty hproper
  by_cases hrow : row.val < 13
  · let pureRow : Fin 13 := ⟨row.val, hrow⟩
    have hroweq : row = pureRow.castSucc := Fin.ext rfl
    rw [hroweq]
    refine ⟨pureChildProfile pureRow,
      ⟨pureOutside pureRow, by simpa using pureOutside_not_mem pureRow⟩,
      pureChild_terminalNash pureRow, pureChild_jointNever_eq_zero pureRow, ?_⟩
    change 0 < quittingTerminalPayoff survivorReward
        (Function.update (pureQuietLift pureRow) (pureOutside pureRow)
          (quittingPureTimeBehaviorStrategy survivorReward (pureOutside pureRow) (some 0)))
        (pureOutside pureRow) -
      quittingTerminalPayoff survivorReward (pureQuietLift pureRow) (pureOutside pureRow)
    rw [pureQuietLift_quitNow_gain_eq]
    split_ifs <;> norm_num [loss]
  · have hroweq : row = 13 := Fin.ext (by omega)
    subst row
    have hcarrier : (childSet 13)ᶜ = ({0} : Finset Player) := by decide
    rw [hcarrier]
    refine ⟨cyclicChildProfile, ⟨0, by decide⟩,
      cyclicChild_terminalNash, cyclicChild_jointNever_eq_zero, ?_⟩
    change 0 < quittingTerminalPayoff survivorReward
        (Function.update cyclicQuietLift 0
          (quittingPureTimeBehaviorStrategy survivorReward 0 (some 0))) 0 -
      quittingTerminalPayoff survivorReward cyclicQuietLift 0
    rw [cyclicQuietLift_quitNow_gain_eq]
    norm_num [loss]

/-- No raw operation kind, nor its advancing-only subcase, protects every
profile of this child. The obstructing outsider is chosen from actual data. -/
theorem exists_outside_no_quiet_certificate (selected : Finset Player)
    (hnonempty : selected.Nonempty) (hproper : selected ≠ Finset.univ) :
    ∃ outside : {who : Player // who ∈ selectedᶜ},
      (∀ kind : WithdrawalFutureJoinKind,
        ¬ Nonempty (WithdrawalFutureJoinRewardCertificate kind
          (quittingChildWithOutsiderReward survivorReward
            (fun who => who ∈ selectedᶜ) outside))) ∧
      ¬ Nonempty (CappedClockParentFutureJoinCertificate
        (quittingChildWithOutsiderReward survivorReward
          (fun who => who ∈ selectedᶜ) outside)) := by
  obtain ⟨profile, outside, hnash, hnever, hgain⟩ :=
    exists_unsafe_exact_child selected hnonempty hproper
  let : Nonempty (QuittingChildPlayer (fun who : Player => who ∈ selectedᶜ)) := by
    obtain ⟨who, hwho⟩ := hnonempty
    exact ⟨⟨who, by simpa using hwho⟩⟩
  have hcap : quittingTerminalPayoff survivorReward
      (Function.update (quittingLiftDeletedProfile survivorReward
          (fun who => who ∈ selectedᶜ) profile) outside.1
        (quittingPureTimeBehaviorStrategy survivorReward outside.1 (some 0))) outside.1 ≤
      quittingBehaviorDeviationPayoffCap survivorReward
        (quittingLiftDeletedProfile survivorReward (fun who => who ∈ selectedᶜ) profile)
        outside.1 := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    exact le_quittingBestReplyValue _ _ _ _
  have hpositive : 0 < quittingBehaviorDeviationPayoffCap survivorReward
      (quittingLiftDeletedProfile survivorReward (fun who => who ∈ selectedᶜ) profile)
      outside.1 - quittingTerminalPayoff survivorReward
        (quittingLiftDeletedProfile survivorReward (fun who => who ∈ selectedᶜ) profile)
        outside.1 := hgain.trans_le (sub_le_sub_right hcap _)
  refine ⟨outside, ?_, ?_⟩
  · intro kind ⟨certificate⟩
    have hbound :=
      quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin
        (fun who : Player => who ∈ selectedᶜ) survivorReward outside kind certificate profile
    simp_rw [quittingBehaviorDeviationDebt_eq_zero_of_exact_terminalNash
      (quittingDeleteBlockReward survivorReward selectedᶜ) profile hnash] at hbound
    simp only [mul_zero, Finset.sum_const_zero, hnever, zero_add] at hbound
    exact (not_lt_of_ge hbound) hpositive
  · rintro ⟨certificate⟩
    have hbound := quittingLiftDeletedProfile_outsideDebt_le_of_cappedClockFutureJoin
      (fun who : Player => who ∈ selectedᶜ) survivorReward outside certificate profile
    simp_rw [quittingBehaviorDeviationDebt_eq_zero_of_exact_terminalNash
      (quittingDeleteBlockReward survivorReward selectedᶜ) profile hnash] at hbound
    simp only [mul_zero, Finset.sum_const_zero, hnever, zero_add] at hbound
    exact (not_lt_of_ge hbound) hpositive

/-! ## Literal advancing-only finite-row crosschecks -/

def AdvancingFutureRow (selected : Finset Player) (outside : Player)
    (weight : Player → ℝ) (background : Finset Player) : Prop :=
  quittingSoloReward survivorReward outside outside -
      quittingSetReward survivorReward background outside ≤
    ∑ who ∈ selected, weight who *
      (quittingSoloReward survivorReward who who -
        quittingSetReward survivorReward background who)

def AdvancingJoinRow (selected : Finset Player) (outside : Player)
    (weight : Player → ℝ) (background : Finset Player) : Prop :=
  quittingSetReward survivorReward (insert outside background) outside -
      quittingSetReward survivorReward background outside ≤
    ∑ who ∈ selected, weight who *
      (quittingSetReward survivorReward (insert who background) who -
        quittingSetReward survivorReward background who)

theorem advancing_future_rows_123_iff (weight : Player → ℝ) :
    (AdvancingFutureRow {1, 2, 3} 0 weight {1} ∧
      AdvancingFutureRow {1, 2, 3} 0 weight {2} ∧
      AdvancingFutureRow {1, 2, 3} 0 weight {3}) ↔
    (-1 ≤ -3 * weight 2 + weight 3 ∧
      -1 ≤ weight 1 - 3 * weight 3 ∧ 1 ≤ -3 * weight 1 + weight 2) := by
  norm_num [AdvancingFutureRow, quittingSoloReward, quittingSingletonTerminal,
    quittingSetReward, survivorReward, lower, upper, Finset.ext_iff, Fin.forall_fin_succ]
  ring_nf

theorem no_advancing_future_rows_123 (weight : Player → ℝ)
    (hweight : 0 ≤ weight 1) :
    ¬ (AdvancingFutureRow {1, 2, 3} 0 weight {1} ∧
      AdvancingFutureRow {1, 2, 3} 0 weight {2} ∧
      AdvancingFutureRow {1, 2, 3} 0 weight {3}) := by
  rw [advancing_future_rows_123_iff]
  rintro ⟨h1, h2, h3⟩
  linarith

theorem no_advancing_future_row_023 (weight : Player → ℝ)
    (hzero : 0 ≤ weight 0) (hthree : 0 ≤ weight 3) :
    ¬ AdvancingFutureRow {0, 2, 3} 1 weight {2} := by
  intro hrow
  norm_num [AdvancingFutureRow, quittingSoloReward, quittingSingletonTerminal,
    quittingSetReward, survivorReward, lower, upper, Finset.ext_iff, Fin.forall_fin_succ] at hrow
  linarith

theorem no_advancing_future_row_012 (weight : Player → ℝ)
    (hzero : 0 ≤ weight 0) (htwo : 0 ≤ weight 2) :
    ¬ AdvancingFutureRow {0, 1, 2} 3 weight {1} := by
  intro hrow
  norm_num [AdvancingFutureRow, quittingSoloReward, quittingSingletonTerminal,
    quittingSetReward, survivorReward, lower, upper, Finset.ext_iff, Fin.forall_fin_succ] at hrow
  linarith

theorem no_advancing_join_row_013 (weight : Player → ℝ)
    (hweight : 0 ≤ weight 1) :
    ¬ AdvancingJoinRow {0, 1, 3} 2 weight {0, 3} := by
  intro hrow
  norm_num [AdvancingJoinRow, quittingSetReward, survivorReward, lower, upper, loss,
    Finset.ext_iff, Fin.forall_fin_succ] at hrow
  linarith

end GameTheory.NegativePremiumCyclicChild.Fixtures.Children
