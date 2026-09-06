import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import UniformEquilibrium.Quitting.Root.NashDefect
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers

/-! # A supplied sure root need not repeat against its own payoff -/

noncomputable section

namespace GameTheory.SureRootNonrepeatability

open Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who ↦
    if who = 0 then
      if 1 ∈ terminal.1 then if 0 ∈ terminal.1 then 3 else 2 else 1
    else 0

def root : Fin 4 → PMF Bool :=
  quittingSureSetOwnerRoot {0} 1 (1 / 4) (by norm_num) (by norm_num)

def punishment : Payoff (Fin 4) := ![1, 0, 0, 0]
def terminalValue : Payoff (Fin 4) := ![3 / 2, 0, 0, 0]

theorem one_le_stationaryFixedOpponentsQuitValue
    (opponents : Fin 4 → PMF Bool) :
    1 ≤ quittingStationaryFixedOpponentsQuitValue reward opponents 0 := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [← pmfPi_bind_update_pure opponents 0 true, expect_bind]
  simp only [expect_pure]
  calc
    (1 : ℝ) = expect (pmfPi opponents) (fun _ ↦ 1) :=
      (expect_const _ 1).symm
    _ ≤ _ := by
      apply expect_mono
      intro action
      unfold quittingRootPayoff
      rw [dif_pos]
      · simp [reward, quittingQuitters, Function.update]
        split_ifs <;> norm_num
      · exact ⟨0, by simp [quittingQuitters, Function.update]⟩

theorem singletonSelfReward (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = punishment who := by
  fin_cases who <;>
    simp [reward, punishment, quittingSingletonTerminal]

theorem punishmentValue_eq_punishment (who : Fin 4) :
    quittingPunishmentValue reward who = punishment who := by
  apply le_antisymm
  · have hupper := quittingPunishmentValue_le_max_solo reward who
    rw [quittingSetReward_singleton_eq_soloReward] at hupper
    fin_cases who <;>
      simpa [quittingSoloReward, reward, punishment] using hupper
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    unfold quittingStationaryPunishmentValue
    fin_cases who
    · apply le_ciInf
      intro opponents
      refine (one_le_stationaryFixedOpponentsQuitValue opponents).trans ?_
      exact le_max_left _ _
    · apply le_ciInf
      intro opponents
      exact le_quittingStationaryUnilateralCap_of_forall_le reward 1 le_rfl
        (by intro terminal; simp [reward]) opponents
    · apply le_ciInf
      intro opponents
      exact le_quittingStationaryUnilateralCap_of_forall_le reward 2 le_rfl
        (by intro terminal; simp [reward]) opponents
    · apply le_ciInf
      intro opponents
      exact le_quittingStationaryUnilateralCap_of_forall_le reward 3 le_rfl
        (by intro terminal; simp [reward]) opponents

theorem isNormal (who : Fin 4) : IsQuittingNormalPlayer reward who := by
  rw [IsQuittingNormalPlayer, punishmentValue_eq_punishment]
  rw [← singletonSelfReward]
  rfl

theorem root_quitProbability (who : Fin 4) :
    (root who true).toReal = ![1, 1 / 4, 0, 0] who := by
  fin_cases who <;>
    simp [root, quittingSureSetOwnerRoot, quittingPureSetRoot,
      quittingSetAction]

@[simp] theorem absorptionMass_eq_one :
    quittingRootAbsorptionMass root = 1 := by
  rw [quittingRootAbsorptionMass]
  unfold root
  rw [stationaryContinueMass_sureSetOwnerRoot_of_nonempty]
  · norm_num
  · simp
  · simp

theorem successor (tail : Payoff (Fin 4)) :
    quittingRootSuccessorPayoff reward tail root = terminalValue := by
  funext who
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  unfold root
  rw [quittingRootAbsorbingContribution_sureSetOwnerRoot]
  · rw [stationaryContinueMass_sureSetOwnerRoot_of_nonempty]
    · fin_cases who <;>
        simp [quittingSureSetOwnerValue, quittingSetReward, reward,
          terminalValue]; norm_num
    · simp
    · simp
  · simp

theorem quitPayoff (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootQuitPayoff reward tail root who = terminalValue who := by
  rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward (fun _ ↦ root) who tail 0]
  change quittingStationaryFixedOpponentsQuitValue reward root who = _
  unfold root
  by_cases hwho : who = 1
  · subst who
    rw [fixedOpponentsQuitValue_sureSetOwnerRoot_owner]
    simp [quittingSetReward, reward, terminalValue]
  · rw [fixedOpponentsQuitValue_sureSetOwnerRoot_other]
    · fin_cases who <;>
        simp_all [quittingSureSetOwnerValue, quittingSetReward, reward,
          terminalValue]; norm_num
    · simp
    · exact hwho

theorem continuePayoff (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootContinuePayoff reward tail root who =
      if who = 0 then 1 / 2 + (3 / 4) * tail 0 else 0 := by
  rw [quittingRootContinuePayoff_eq_fixedOpponents
    reward (fun _ ↦ root) who tail 0]
  change quittingStationaryFixedOpponentsContinueReward reward root who +
      quittingStationaryFixedOpponentsContinueMass root who * tail who = _
  unfold root
  by_cases howner : who = 1
  · subst who
    rw [fixedOpponentsContinueReward_sureSetOwnerRoot_owner]
    · rw [fixedOpponentsContinueMass_sureSetOwnerRoot_owner]
      · simp [quittingSetReward, reward]
      · simp
      · simp
    · simp
  · rw [fixedOpponentsContinueReward_sureSetOwnerRoot_other]
    · fin_cases who
      · unfold quittingStationaryFixedOpponentsContinueMass
          quittingFixedOpponentsContinueMass
        rw [update_sureSetOwnerRoot_other_false]
        · change quittingSureSetOwnerValue reward ∅ 1 (1 / 4) 0 +
              quittingStationaryContinueMass
                (quittingSureSetOwnerRoot ∅ 1 (1 / 4)
                  (by norm_num) (by norm_num)) * tail 0 = _
          rw [stationaryContinueMass_sureSetOwnerRoot_empty]
          simp [quittingSureSetOwnerValue, quittingSetReward, reward]
          ring
        · simp
      · simp at howner
      · rw [fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_nonempty]
        · simp [quittingSureSetOwnerValue, quittingSetReward, reward]
        · simp
        · simp
        · simp
      · rw [fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_nonempty]
        · simp [quittingSureSetOwnerValue, quittingSetReward, reward]
        · simp
        · simp
        · simp
    · simp
    · exact howner

@[simp] theorem coordinateNashDefect_zeroTail (who : Fin 4) :
    quittingRootCoordinateNashDefect reward (fun _ ↦ 0) root who = 0 := by
  rw [quittingRootCoordinateNashDefect, quitPayoff, continuePayoff]
  have hsuccessor := congrFun (successor (fun _ ↦ 0)) who
  rw [hsuccessor]
  fin_cases who <;> simp [terminalValue]; norm_num

/-- The supplied root is exact one-stage Nash against the zero continuation annotation. -/
theorem exactNash_followedByNever :
    IsεQuittingRootNash reward (fun _ ↦ 0) 0 root := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  exact coordinateNashDefect_zeroTail

theorem owner_quitPayoff :
    quittingRootQuitPayoff reward punishment root 0 = 3 / 2 := by
  rw [quitPayoff]
  simp [terminalValue]

theorem owner_absorbingContribution :
    quittingRootAbsorbingContribution reward root 0 = 3 / 2 := by
  have hsuccessor := congrFun (successor punishment) 0
  have hcontinue : quittingStationaryContinueMass root = 0 := by
    have habs := absorptionMass_eq_one
    unfold quittingRootAbsorptionMass at habs
    linarith
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    hcontinue] at hsuccessor
  simpa [terminalValue] using hsuccessor

theorem owner_continuePayoff_punishment :
    quittingRootContinuePayoff reward punishment root 0 = 5 / 4 := by
  rw [continuePayoff]
  simp [punishment]
  norm_num

theorem owner_continuePayoff_terminalValue :
    quittingRootContinuePayoff reward terminalValue root 0 = 13 / 8 := by
  rw [continuePayoff]
  simp [terminalValue]
  norm_num

theorem owner_fixedOpponentsContinueReward :
    quittingStationaryFixedOpponentsContinueReward reward root 0 = 1 / 2 := by
  unfold root
  rw [fixedOpponentsContinueReward_sureSetOwnerRoot_other]
  · simp [quittingSureSetOwnerValue, quittingSetReward, reward]
    norm_num
  · simp
  · norm_num

theorem owner_fixedOpponentsContinueMass :
    quittingStationaryFixedOpponentsContinueMass root 0 = 3 / 4 := by
  unfold root
  rw [fixedOpponentsContinueMass_sureSetOwnerRoot_other_of_erase_empty]
  · norm_num
  · norm_num
  · simp

@[simp] theorem coordinateNashDefect_punishment (who : Fin 4) :
    quittingRootCoordinateNashDefect reward punishment root who = 0 := by
  rw [quittingRootCoordinateNashDefect, quitPayoff, continuePayoff]
  have hsuccessor := congrFun (successor punishment) who
  rw [hsuccessor]
  fin_cases who <;>
    simp [terminalValue, punishment]; norm_num

/-- The supplied root remains Nash against the punishment tail. -/
theorem exactNash_punishment :
    IsεQuittingRootNash reward punishment 0 root := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  exact coordinateNashDefect_punishment

def suppliedProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward root
    (quittingAlwaysContinueProfile reward)

theorem alwaysContinue_bestResponse_eq_punishment :
    quittingContinuationBestResponse reward
      (quittingAlwaysContinueProfile reward) = punishment := by
  funext who
  unfold quittingContinuationBestResponse
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  fin_cases who <;>
    simp [reward, punishment, quittingSingletonTerminal]

theorem suppliedProfile_terminalPayoff :
    quittingTerminalPayoff reward suppliedProfile = terminalValue := by
  funext who
  unfold suppliedProfile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  change quittingRootSuccessorPayoff reward
    (fun player ↦ quittingTerminalPayoff reward
      (quittingAlwaysContinueProfile reward) player) root who = terminalValue who
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  exact congrFun (successor (fun _ ↦ 0)) who

/-- The actual root-then-Never behavioral profile is an exact terminal Nash
profile and has the displayed terminal payoff. -/
theorem suppliedProfile_exactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 suppliedProfile := by
  unfold suppliedProfile
  apply isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
  · unfold root
    exact rootHasSureQuitter_quittingSureSetOwnerRoot
      (sure := 0) (by simp) (by simp) (1 / 4) (by norm_num) (by norm_num)
  · rw [alwaysContinue_bestResponse_eq_punishment]
    exact exactNash_punishment

/-- Repeating the supplied root against its own terminal payoff gives player
zero the strict one-stage gain `1/8`. -/
theorem owner_coordinateNashDefect_terminalValue :
    quittingRootCoordinateNashDefect reward terminalValue root 0 = 1 / 8 := by
  rw [quittingRootCoordinateNashDefect, quitPayoff, continuePayoff]
  have hsuccessor := congrFun (successor terminalValue) 0
  rw [hsuccessor]
  simp [terminalValue]
  norm_num

theorem not_exactNash_terminalValue :
    ¬IsεQuittingRootNash reward terminalValue 0 root := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  intro hall
  have hzero := hall 0
  rw [owner_coordinateNashDefect_terminalValue] at hzero
  norm_num at hzero

/-! The same reward table also has a different exact constant source. -/

def constantRoot : Fin 4 → PMF Bool := quittingPureSetRoot {0, 1}
def constantValue : Payoff (Fin 4) := ![3, 0, 0, 0]

theorem constantQuitters_nonempty : ({0, 1} : Finset (Fin 4)).Nonempty := by
  simp

theorem constantQuitters_erase_nonempty (who : Fin 4) :
    (({0, 1} : Finset (Fin 4)).erase who).Nonempty := by
  fin_cases who
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

@[simp] theorem constantRoot_successor (tail : Payoff (Fin 4)) :
    quittingRootSuccessorPayoff reward tail constantRoot = constantValue := by
  funext who
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  unfold constantRoot
  rw [quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty constantQuitters_nonempty]
  fin_cases who <;>
    simp [quittingSetReward, reward, constantValue]

@[simp] theorem constantRoot_coordinateNashDefect
    (tail : Payoff (Fin 4)) (who : Fin 4) :
    quittingRootCoordinateNashDefect reward tail constantRoot who = 0 := by
  rw [quittingRootCoordinateNashDefect]
  have hsuccessor := congrFun (constantRoot_successor tail) who
  rw [hsuccessor]
  unfold constantRoot
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
      tail {0, 1} who (constantQuitters_erase_nonempty who)]
  fin_cases who <;>
    simp [quittingSetReward, reward, constantValue]; norm_num

theorem constantRoot_exactNash :
    IsεQuittingRootNash reward constantValue 0 constantRoot := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  exact constantRoot_coordinateNashDefect constantValue

theorem constantRoot_exactBellman :
    quittingRootSuccessorPayoff reward constantValue constantRoot =
      constantValue :=
  constantRoot_successor constantValue

end GameTheory.SureRootNonrepeatability
