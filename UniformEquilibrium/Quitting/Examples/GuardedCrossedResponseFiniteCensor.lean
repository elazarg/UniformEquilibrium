import UniformEquilibrium.Quitting.Stationary.FiniteCensor
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseFiniteHorizon

/-! # Literal sharp finite censor bounds at the half-ceiling crossed-response root -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open _root_.Math.Probability _root_.Math.PMFProduct

/-- The maximum deleted-opponent survival is the third coordinate, `7/12`. -/
theorem halfCeilingRoot_deletedSurvivalMax :
    quittingStationaryDeletedSurvivalMax halfCeilingRoot = 7 / 12 := by
  apply le_antisymm
  · unfold quittingStationaryDeletedSurvivalMax
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
    intro player _
    cases player with
    | none => norm_num
    | some who =>
        change quittingStationaryFixedOpponentsContinueMass halfCeilingRoot who ≤ 7 / 12
        rw [halfCeilingRoot_deletedSurvival]
        fin_cases who <;> norm_num
  · have h := quittingStationaryFixedOpponentsContinueMass_le_max halfCeilingRoot 2
    rw [halfCeilingRoot_deletedSurvival] at h
    simpa using h

/-- The displayed half-ceiling root itself supplies the finite clocks. Their terminal
regret is `(597/7)(7/12)^N`, not a sum of marginal tails; the same clocks satisfy
the signed `N+1` horizon estimates. No root or equilibrium is supplied by the caller. -/
theorem exists_halfCeilingFiniteCensorTimingProfile
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        censorLateFiniteStoppingLaw
          (quittingBehaviorStoppingLaw halfCeilingReward
            (quittingStationaryProfile halfCeilingReward halfCeilingRoot who))
          (deadline - 1)) ∧
      quittingTerminalSemanticPair halfCeilingReward
          (quittingFiniteDeadlineTimingProfile halfCeilingReward deadline mixed) =
        quittingTerminalSemanticPair halfCeilingReward
          (quittingStationaryFiniteCensorProfile halfCeilingReward halfCeilingRoot deadline) ∧
      (∀ who time, time < deadline →
        ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF (some time)).toReal =
          halfCeilingHazard who * (1 - halfCeilingHazard who) ^ time) ∧
      (∀ who, (mixed who none).toReal = (1 - halfCeilingHazard who) ^ deadline) ∧
      (∀ who, quittingTerminalPayoff halfCeilingReward
          (quittingFiniteDeadlineTimingProfile halfCeilingReward deadline mixed) who =
        (1 - (7 / 18 : ℝ) ^ deadline) * halfCeilingValue who) ∧
      (quittingGame halfCeilingReward).IsεAsymptoticNash
        (quittingTerminalPayoff halfCeilingReward)
        ((597 / 7) * (7 / 12 : ℝ) ^ deadline)
        (quittingFiniteDeadlineTimingProfile halfCeilingReward deadline mixed) ∧
      (∀ who, |quittingTerminalPayoff halfCeilingReward
          (quittingFiniteDeadlineTimingProfile halfCeilingReward deadline mixed) who -
        halfCeilingValue who| ≤ (199 / 7) * (7 / 12 : ℝ) ^ deadline) ∧
      ∀ horizon, 0 < horizon →
        (quittingGame halfCeilingReward).IsεHorizonNash none horizon
          ((597 / 7) * (7 / 12 : ℝ) ^ deadline +
            2 * (199 / 7) * (deadline + 1) / horizon)
          (quittingFiniteDeadlineTimingProfile halfCeilingReward deadline mixed) ∧
        ∀ who, |(quittingGame halfCeilingReward).finiteAveragePayoff none horizon
            (quittingFiniteDeadlineTimingProfile halfCeilingReward deadline mixed) who -
          halfCeilingValue who| ≤
            (199 / 7) * (7 / 12 : ℝ) ^ deadline +
              (199 / 7) * (deadline + 1) / horizon := by
  obtain ⟨_, mixed, hlaws, hpair, hfinite, hnever, hpay, hnash, hdelivery, hhorizon⟩ :=
    exists_stationaryFiniteCensorTimingProfile halfCeilingReward halfCeilingRoot
      deadline hdeadline halfCeiling_abs_reward_le halfCeilingRoot_terminalNash
      halfCeilingRoot_contracts
  have htrue (who : Fin 4) : (halfCeilingRoot who true).toReal = halfCeilingHazard who :=
    congrFun halfCeilingRoot_hazard who
  have hfalse (who : Fin 4) :
      (halfCeilingRoot who false).toReal = 1 - halfCeilingHazard who := by
    rw [pmfBool_false_toReal, htrue]
  have hcoefficient : 3 * (199 / 7 : ℝ) = 597 / 7 := by norm_num
  refine ⟨mixed, hlaws, hpair, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro who time htime
    simpa only [htrue, hfalse] using hfinite who time htime
  · intro who
    simpa only [hfalse] using hnever who
  · simpa only [halfCeilingRoot_jointSurvival, halfCeilingRoot_terminalPayoff] using hpay
  · simpa only [halfCeilingRoot_deletedSurvivalMax, hcoefficient] using hnash
  · simpa only [halfCeilingRoot_deletedSurvivalMax, halfCeilingRoot_terminalPayoff]
      using hdelivery
  · simpa only [halfCeilingRoot_deletedSurvivalMax, halfCeilingRoot_terminalPayoff,
      hcoefficient] using hhorizon

end GameTheory.GuardedCrossedResponseExamples

