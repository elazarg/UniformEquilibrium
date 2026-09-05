import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorptionCompletion
import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorptionNecessity
import UniformEquilibrium.Quitting.Classification.OnePlayer.Existence
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingStageCoalitionMass
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance

/-! # Boundary regressions for finite-menu early absorption -/

noncomputable section

namespace GameTheory.FiniteMenuBoundaryRegressions

open GameTheory StochasticGame

/-- The one-player constant-minus-one quitting table. -/
def negativeOneReward :
    {S : Finset PUnit // S.Nonempty} → Payoff PUnit :=
  fun _ _ => -1

private theorem finiteProfile_eq_stoppingLawProfile
    {deadline : ℕ}
    (reward : {S : Finset PUnit // S.Nonempty} → Payoff PUnit)
    (mixed : PUnit → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteDeadlineTimingProfile reward deadline mixed =
      quittingStoppingLawProfile reward (fun who =>
        (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF) := by
  apply finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
  intro who
  rfl

theorem negativeOne_has_uniformEquilibriumPayoff :
    ∃ payoff : Payoff PUnit,
      (quittingGame negativeOneReward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_onePlayer negativeOneReward

theorem negativeOne_finiteDeadline_payoff
    (deadline : ℕ)
    (mixed : PUnit → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingTerminalPayoff negativeOneReward
        (quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed) PUnit.unit =
      (mixed PUnit.unit none).toReal - 1 := by
  let laws : PUnit → PMF (Option ℕ) := fun who =>
    (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
  rw [finiteProfile_eq_stoppingLawProfile negativeOneReward mixed,
    quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  unfold quittingStoppingLawExpectedPayoff
  let terminalLaw := quittingIndependentTerminalOutcomeLaw laws
  calc
    Math.Probability.expect terminalLaw
          (fun outcome => quittingTerminalOutcomeReward negativeOneReward outcome PUnit.unit) =
        Math.Probability.expect terminalLaw
          (fun outcome => (if outcome = none then 1 else 0) - 1) := by
      congr 1
      funext outcome
      cases outcome <;> simp [quittingTerminalOutcomeReward, negativeOneReward]
    _ =
        Math.Probability.expect terminalLaw
          (fun outcome => if outcome = none then 1 else 0) - 1 := by
      rw [Math.Probability.expect_sub, Math.Probability.expect_const]
    _ = (terminalLaw none).toReal - 1 := by
      rw [← Math.Probability.apply_toReal_eq_expect_indicator]
    _ = (mixed PUnit.unit none).toReal - 1 := by
      congr 2
      unfold terminalLaw quittingIndependentTerminalOutcomeLaw
      rw [PMF.map_apply, tsum_eq_single (fun _ => none)]
      · have hmap : laws PUnit.unit none = mixed PUnit.unit none := by
          unfold laws quittingFiniteDeadlineTimingLaw
          rw [Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
          have hmaps : (mixed PUnit.unit).map quittingFiniteDeadlineTimingActionTime =
              (mixed PUnit.unit).map
                (Math.Probability.finiteStoppingTimeDecode deadline) := by
            congr 1
            funext action
            cases action <;> rfl
          rw [hmaps, PMF.map_apply, tsum_eq_single none]
          · simp [Math.Probability.finiteStoppingTimeDecode]
          · intro action haction
            cases action with
            | none => exact (haction rfl).elim
            | some time => simp [Math.Probability.finiteStoppingTimeDecode]
        simp [quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
          quittingStoppingTimeValue, hmap]
      · intro times htimes
        have htime : times PUnit.unit ≠ none := by
          intro hnone
          apply htimes
          funext who
          simpa [Subsingleton.elim who PUnit.unit] using hnone
        cases h : times PUnit.unit with
        | none => exact (htime h).elim
        | some time =>
            simp [quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
              quittingStoppingTimeValue, h]

theorem negativeOne_finiteDeadline_quitMass_le_error
    (deadline : ℕ)
    (mixed : PUnit → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (error : ℝ)
    (hnash : IsQuittingFiniteDeadlineNash negativeOneReward deadline error mixed) :
    1 - (mixed PUnit.unit none).toReal ≤ error := by
  have hnever := ((isQuittingFiniteDeadlineNash_iff_pure
    negativeOneReward deadline error mixed).mp hnash) PUnit.unit none
  have hzero : quittingTerminalPayoff negativeOneReward
      (Function.update
        (quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed) PUnit.unit
        (quittingPureTimeBehaviorStrategy negativeOneReward PUnit.unit
          (quittingFiniteDeadlineTimingActionTime
            (none : QuittingFiniteDeadlineTimingAction deadline))))
      PUnit.unit = 0 := by
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    apply quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    intro time _
    funext player
    simp [quittingRootSequenceUpdate, quittingPureTimeHazard,
      quittingFiniteDeadlineTimingActionTime, Subsingleton.elim player PUnit.unit]
    change PMF.pure false = PMF.pure false
    rfl
  rw [hzero, negativeOne_finiteDeadline_payoff] at hnever
  linarith

/-- The negative one-player game has a uniform equilibrium but fails the
positive-singleton early-absorption conclusion. -/
theorem negativeOne_not_has_finiteMenuEarlyAbsorption :
    ¬ HasQuittingFiniteMenuEarlyAbsorption negativeOneReward := by
  intro hea
  obtain ⟨deadline, hdeadline, mixed, hnash, hreach⟩ :=
    hea (1 / 4) (by norm_num) 1 (by norm_num) (1 / 2) (by norm_num) 0
  have hnone := negativeOne_finiteDeadline_quitMass_le_error
    deadline mixed (1 / 4) hnash
  have hjoint : quittingJointSurvivalWeight
      (quittingProfileLiveRoot negativeOneReward
        (quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed))
      0 (deadline - 1) =
      quittingHazardSurvival
        (quittingBehaviorLiveHazard negativeOneReward
          (quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed PUnit.unit))
        (deadline - 1) := by
    unfold quittingJointSurvivalWeight quittingHazardSurvival
    rw [quittingFiniteContinueWeight_eq_survivalProduct]
    congr 1
    funext time
    simp [quittingStationaryContinueMass, quittingProfileLiveRoot,
      quittingBehaviorLiveHazard, quittingAllContinueAction]
  have hmono : (mixed PUnit.unit none).toReal ≤
      quittingHazardSurvival
        (quittingBehaviorLiveHazard negativeOneReward
          (quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed PUnit.unit))
        (deadline - 1) := by
    have hbehavior := quittingBehaviorStoppingLaw_compactStoppingLawProfile
      negativeOneReward
      (fun _ => quittingFiniteDeadlineTimingLaw (mixed PUnit.unit)) PUnit.unit
    have hnone : (quittingBehaviorStoppingLaw negativeOneReward
        (quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed PUnit.unit)
        none).toReal = (mixed PUnit.unit none).toReal := by
      rw [show quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed =
          quittingCompactStoppingLawProfile negativeOneReward
            (fun who => quittingFiniteDeadlineTimingLaw (mixed who)) by rfl,
        hbehavior]
      exact congrArg ENNReal.toReal (by
        unfold quittingFiniteDeadlineTimingLaw
        rw [Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
        have hmaps : (mixed PUnit.unit).map quittingFiniteDeadlineTimingActionTime =
            (mixed PUnit.unit).map
              (Math.Probability.finiteStoppingTimeDecode deadline) := by
          congr 1
          funext action
          cases action <;> rfl
        rw [hmaps, PMF.map_apply, tsum_eq_single none]
        · simp [Math.Probability.finiteStoppingTimeDecode]
        · intro action haction
          cases action with
          | none => exact (haction rfl).elim
          | some time => simp [Math.Probability.finiteStoppingTimeDecode])
    rw [← hnone]
    simpa [quittingBehaviorStoppingLaw, quittingBehaviorLiveHazard] using
      quittingHazardNeverMass_le_survival
        (quittingBehaviorLiveHazard negativeOneReward
          (quittingFiniteDeadlineTimingProfile negativeOneReward deadline mixed PUnit.unit))
        (deadline - 1)
  rw [hjoint] at hreach
  norm_num at hnone
  linarith

end GameTheory.FiniteMenuBoundaryRegressions
