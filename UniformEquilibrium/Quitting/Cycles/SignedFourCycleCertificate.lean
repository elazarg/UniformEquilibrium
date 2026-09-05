import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleValues

noncomputable section

namespace GameTheory
namespace SignedFourCycleSingletonData

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable (data : SignedFourCycleSingletonData reward) (tests : data.StrictTests)

private theorem weighted_quotient_eq
    (a b c d denominator x y z t base : ℝ) (hdenominator : denominator ≠ 0)
    (hmass : a + b + c + d = denominator)
    (hbalance : a * (x - base) + b * (y - base) +
      c * (z - base) + d * (t - base) = 0) :
    (a * x + b * y + c * z + d * t) / denominator = base := by
  rw [div_eq_iff hdenominator]
  linear_combination hbalance + base * hmass

private theorem one_sub_period_ne (tests : data.StrictTests) :
    1 - data.coefficients.periodSurvival ≠ 0 :=
  ne_of_gt (sub_pos.mpr (data.coefficients.periodSurvival_lt_one
    (StrictTests.smallerEigenvalue_gt_one tests)))

theorem next_coarse_owner_eq (phase : Fin 4) :
    data.coarseValue tests (finRotate 4 phase) phase =
      quittingSoloReward reward phase phase := by
  let w := tests.weights
  let A := data.coefficients.periodSurvival
  have hbalance := data.weighted_singleton_comparison_balances tests
  have hsum := w.sum_normalizedWeight
  have hAeq : A = 1 - (w.normalizedWeightZero + w.normalizedWeightOne +
      w.normalizedWeightTwo + w.normalizedWeightThree) := by
    dsimp [A, w, StrictTests.weights] at hsum ⊢
    linarith
  obtain ⟨ht1, ht2, ht3, -⟩ := w.tails_pos
  fin_cases phase
  · change data.afterZeroValue tests 0 = _
    apply weighted_quotient_eq
      (A * w.normalizedWeightZero) w.normalizedWeightOne
      w.normalizedWeightTwo w.normalizedWeightThree
      (w.tailOne * (1 - A))
      (quittingSoloReward reward 0 0) (quittingSoloReward reward 1 0)
      (quittingSoloReward reward 2 0) (quittingSoloReward reward 3 0)
      (quittingSoloReward reward 0 0)
    · exact mul_ne_zero (ne_of_gt ht1) (data.one_sub_period_ne tests)
    · rw [hAeq]
      unfold Math.SignedFourCycleStrictData.tailOne
      ring
    · simpa [QuittingLCPClassification.quittingSingletonMatrix,
        quittingSoloReward] using hbalance.1
  · change data.afterOneValue tests 1 = _
    have hresult :
        (A * w.normalizedWeightZero * quittingSoloReward reward 0 1 +
          A * w.normalizedWeightOne * quittingSoloReward reward 1 1 +
          w.normalizedWeightTwo * quittingSoloReward reward 2 1 +
          w.normalizedWeightThree * quittingSoloReward reward 3 1) /
            (w.tailTwo * (1 - A)) = quittingSoloReward reward 1 1 := by
      apply weighted_quotient_eq
      · exact mul_ne_zero (ne_of_gt ht2) (data.one_sub_period_ne tests)
      · rw [hAeq]
        unfold Math.SignedFourCycleStrictData.tailTwo
          Math.SignedFourCycleStrictData.tailOne
        ring
      · convert hbalance.2.1 using 1
        simp [QuittingLCPClassification.quittingSingletonMatrix,
          quittingSoloReward]
        ring
    rw [afterOneValue]
    convert hresult using 1
    · ring
    · congr 2
  · change data.afterTwoValue tests 2 = _
    have hresult :
        (A * w.normalizedWeightZero * quittingSoloReward reward 0 2 +
          A * w.normalizedWeightOne * quittingSoloReward reward 1 2 +
          A * w.normalizedWeightTwo * quittingSoloReward reward 2 2 +
          w.normalizedWeightThree * quittingSoloReward reward 3 2) /
            (w.tailThree * (1 - A)) = quittingSoloReward reward 2 2 := by
      apply weighted_quotient_eq
      · exact mul_ne_zero (ne_of_gt ht3) (data.one_sub_period_ne tests)
      · rw [hAeq]
        unfold Math.SignedFourCycleStrictData.tailThree
          Math.SignedFourCycleStrictData.tailTwo
          Math.SignedFourCycleStrictData.tailOne
        ring
      · convert hbalance.2.2.1 using 1
        simp [QuittingLCPClassification.quittingSingletonMatrix,
          quittingSoloReward]
        ring
    rw [afterTwoValue]
    convert hresult using 1
    · ring
    · congr 2
  · change data.targetValue tests 3 = _
    dsimp [targetValue]
    apply weighted_quotient_eq w.normalizedWeightZero w.normalizedWeightOne
      w.normalizedWeightTwo w.normalizedWeightThree (1 - A)
      (quittingSoloReward reward 0 3) (quittingSoloReward reward 1 3)
      (quittingSoloReward reward 2 3) (quittingSoloReward reward 3 3)
      (quittingSoloReward reward 3 3)
    · exact data.one_sub_period_ne tests
    · simpa [w, A, StrictTests.weights] using hsum
    · have hA : A ≠ 0 := ne_of_gt
        (data.coefficients.periodSurvival_pos
          (StrictTests.smallerEigenvalue_gt_one tests))
      have hwrapped := hbalance.2.2.2
      have hunwrapped :
          w.normalizedWeightZero *
                QuittingLCPClassification.quittingSingletonMatrix reward 3 0 +
              w.normalizedWeightOne *
                QuittingLCPClassification.quittingSingletonMatrix reward 3 1 +
            w.normalizedWeightTwo *
              QuittingLCPClassification.quittingSingletonMatrix reward 3 2 = 0 := by
        exact (mul_eq_zero.mp hwrapped).resolve_left hA
      simpa [QuittingLCPClassification.quittingSingletonMatrix,
        quittingSoloReward] using hunwrapped

theorem coarse_active (phase : Fin 4) :
    data.coarseValue tests phase phase = quittingSoloReward reward phase phase := by
  rw [data.coarse_bellman tests phase]
  change data.phaseHazard tests phase * quittingSoloReward reward phase phase +
      (1 - data.phaseHazard tests phase) *
        data.coarseValue tests (finRotate 4 phase) phase = _
  rw [data.next_coarse_owner_eq tests phase]
  ring

theorem phaseHazard_pos_and_lt_one (phase : Fin 4) :
    0 < data.phaseHazard tests phase ∧ data.phaseHazard tests phase < 1 := by
  have h := tests.weights.hazard_pos_and_lt_one
  fin_cases phase
  · simpa [phaseHazard] using h.1
  · simpa [phaseHazard] using h.2.1
  · simpa [phaseHazard] using h.2.2.1
  · simpa [phaseHazard] using h.2.2.2

theorem coarse_two_after_owner_gt (owner : Fin 4) :
    quittingSoloReward reward owner owner <
      data.coarseValue tests (owner + 2) owner := by
  have hhazard := data.phaseHazard_pos_and_lt_one tests (owner + 1)
  have harc := congrFun (data.coarse_bellman tests (owner + 1)) owner
  have hprevious := data.next_coarse_owner_eq tests owner
  have hsuccessor := data.successor owner
  fin_cases owner
  all_goals simp [finRotate_apply, coarseValue, phaseHazard] at hhazard harc hprevious hsuccessor
  all_goals simp [coarseValue]
  all_goals unfold QuittingLCPClassification.quittingSingletonMatrix at hsuccessor
  all_goals dsimp [quittingSingletonArcPayoff] at harc
  all_goals unfold quittingSoloReward at harc hprevious ⊢
  all_goals nlinarith [data.b_pos 0, data.b_pos 1, data.b_pos 2,
    data.b_pos 3, hhazard.1, hhazard.2]

theorem coarse_three_after_owner_gt (owner : Fin 4) :
    quittingSoloReward reward owner owner <
      data.coarseValue tests (owner + 3) owner := by
  have hhazard := data.phaseHazard_pos_and_lt_one tests (owner + 3)
  have harc := congrFun (data.coarse_bellman tests (owner + 3)) owner
  have hactive := data.coarse_active tests owner
  have hpredecessor := data.predecessor owner
  fin_cases owner
  all_goals simp [finRotate_apply, coarseValue, phaseHazard] at hhazard harc hactive hpredecessor
  all_goals simp [coarseValue]
  all_goals unfold QuittingLCPClassification.quittingSingletonMatrix at hpredecessor
  all_goals dsimp [quittingSingletonArcPayoff] at harc
  all_goals unfold quittingSoloReward at harc hactive ⊢
  all_goals nlinarith [data.h_pos 0, data.h_pos 1, data.h_pos 2,
    data.h_pos 3, hhazard.1, hhazard.2]

theorem coarse_soloFloor (phase who : Fin 4) :
    quittingSoloReward reward who who ≤ data.coarseValue tests phase who := by
  fin_cases who <;> fin_cases phase
  all_goals first
    | exact (data.coarse_active tests _).ge
    | exact (data.next_coarse_owner_eq tests _).ge
    | exact (data.coarse_two_after_owner_gt tests _).le
    | exact (data.coarse_three_after_owner_gt tests _).le

def certificate : BalancedSingletonCycleCertificate (L := 4) reward where
  owner := id
  hazard := data.phaseHazard tests
  coarse := data.coarseValue tests
  initial := 0
  hazard_nonneg := fun phase => (data.phaseHazard_pos_and_lt_one tests phase).1.le
  hazard_lt_one := fun phase => (data.phaseHazard_pos_and_lt_one tests phase).2
  arc := data.coarse_bellman tests
  active := data.coarse_active tests
  soloFloor := data.coarse_soloFloor tests
  opponentDivergence := by
    intro who
    refine ⟨who + 1, ?_, (data.phaseHazard_pos_and_lt_one tests (who + 1)).1⟩
    fin_cases who <;> decide

/-- The geometric-resolvent target constructed from the raw signed table is
a fixed uniform-equilibrium payoff against unrestricted behavioral deviations. -/
theorem targetValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none (data.targetValue tests) := by
  simpa [certificate, coarseValue] using (data.certificate tests).isUniformEquilibriumPayoff

end SignedFourCycleSingletonData
end GameTheory
