import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate
import UniformEquilibrium.Quitting.Cycles.FourPhaseSingletonValues
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter

/-! # Branch-independent four-phase singleton cycle compiler

Positive masses and their displayed singleton balances supply the owner
equalities and floors. Spectral raw-table construction is supplied by adapters.
-/

noncomputable section

namespace GameTheory
namespace FourPhaseSingletonValues

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
def HasSingletonBalance
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (mass : Math.FourPhasePositiveMass) : Prop :=
  mass.normalizedWeightOne *
      QuittingLCPClassification.quittingSingletonMatrix reward 0 1 +
    mass.normalizedWeightTwo *
      QuittingLCPClassification.quittingSingletonMatrix reward 0 2 +
    mass.normalizedWeightThree *
      QuittingLCPClassification.quittingSingletonMatrix reward 0 3 = 0 ∧
  mass.normalizedWeightTwo *
      QuittingLCPClassification.quittingSingletonMatrix reward 1 2 +
    mass.normalizedWeightThree *
      QuittingLCPClassification.quittingSingletonMatrix reward 1 3 +
    mass.periodSurvival * mass.normalizedWeightZero *
      QuittingLCPClassification.quittingSingletonMatrix reward 1 0 = 0 ∧
  mass.normalizedWeightThree *
      QuittingLCPClassification.quittingSingletonMatrix reward 2 3 +
    mass.periodSurvival *
      (mass.normalizedWeightZero *
          QuittingLCPClassification.quittingSingletonMatrix reward 2 0 +
        mass.normalizedWeightOne *
          QuittingLCPClassification.quittingSingletonMatrix reward 2 1) = 0 ∧
  mass.periodSurvival *
    (mass.normalizedWeightZero *
        QuittingLCPClassification.quittingSingletonMatrix reward 3 0 +
      mass.normalizedWeightOne *
        QuittingLCPClassification.quittingSingletonMatrix reward 3 1 +
      mass.normalizedWeightTwo *
        QuittingLCPClassification.quittingSingletonMatrix reward 3 2) = 0

variable (data : SignedFourCycleSingletonData reward) (mass : Math.FourPhasePositiveMass)
variable (hbalances : HasSingletonBalance reward mass)

private theorem weighted_quotient_eq
    (a b c d denominator x y z t base : ℝ) (hdenominator : denominator ≠ 0)
    (hmass : a + b + c + d = denominator)
    (hbalance : a * (x - base) + b * (y - base) +
      c * (z - base) + d * (t - base) = 0) :
    (a * x + b * y + c * z + d * t) / denominator = base := by
  rw [div_eq_iff hdenominator]
  linear_combination hbalance + base * hmass

private theorem one_sub_period_ne (mass : Math.FourPhasePositiveMass) :
    1 - mass.periodSurvival ≠ 0 :=
  ne_of_gt (sub_pos.mpr mass.periodSurvival_lt_one)

include hbalances

theorem next_coarse_owner_eq (phase : Fin 4) :
    coarseValue reward mass (finRotate 4 phase) phase =
      quittingSoloReward reward phase phase := by
  let w := mass
  let A := mass.periodSurvival
  have hbalance := hbalances
  have hsum := w.sum_normalizedWeight
  have hAeq : A = 1 - (w.normalizedWeightZero + w.normalizedWeightOne +
      w.normalizedWeightTwo + w.normalizedWeightThree) := by
    dsimp [A, w] at hsum ⊢
    linarith
  obtain ⟨ht1, ht2, ht3, -⟩ := w.tails_pos
  fin_cases phase
  · change afterZeroValue reward mass 0 = _
    apply weighted_quotient_eq
      (A * w.normalizedWeightZero) w.normalizedWeightOne
      w.normalizedWeightTwo w.normalizedWeightThree
      (w.tailOne * (1 - A))
      (quittingSoloReward reward 0 0) (quittingSoloReward reward 1 0)
      (quittingSoloReward reward 2 0) (quittingSoloReward reward 3 0)
      (quittingSoloReward reward 0 0)
    · exact mul_ne_zero (ne_of_gt ht1) (one_sub_period_ne mass)
    · rw [hAeq]
      unfold Math.FourPhasePositiveMass.tailOne
      ring
    · simpa [QuittingLCPClassification.quittingSingletonMatrix,
        quittingSoloReward] using hbalance.1
  · change afterOneValue reward mass 1 = _
    have hresult :
        (A * w.normalizedWeightZero * quittingSoloReward reward 0 1 +
          A * w.normalizedWeightOne * quittingSoloReward reward 1 1 +
          w.normalizedWeightTwo * quittingSoloReward reward 2 1 +
          w.normalizedWeightThree * quittingSoloReward reward 3 1) /
            (w.tailTwo * (1 - A)) = quittingSoloReward reward 1 1 := by
      apply weighted_quotient_eq
      · exact mul_ne_zero (ne_of_gt ht2) (one_sub_period_ne mass)
      · rw [hAeq]
        unfold Math.FourPhasePositiveMass.tailTwo
          Math.FourPhasePositiveMass.tailOne
        ring
      · convert hbalance.2.1 using 1
        simp [QuittingLCPClassification.quittingSingletonMatrix,
          quittingSoloReward]
        ring
    rw [afterOneValue]
    convert hresult using 1
    · ring
    · congr 2
  · change afterTwoValue reward mass 2 = _
    have hresult :
        (A * w.normalizedWeightZero * quittingSoloReward reward 0 2 +
          A * w.normalizedWeightOne * quittingSoloReward reward 1 2 +
          A * w.normalizedWeightTwo * quittingSoloReward reward 2 2 +
          w.normalizedWeightThree * quittingSoloReward reward 3 2) /
            (w.tailThree * (1 - A)) = quittingSoloReward reward 2 2 := by
      apply weighted_quotient_eq
      · exact mul_ne_zero (ne_of_gt ht3) (one_sub_period_ne mass)
      · rw [hAeq]
        unfold Math.FourPhasePositiveMass.tailThree
          Math.FourPhasePositiveMass.tailTwo
          Math.FourPhasePositiveMass.tailOne
        ring
      · convert hbalance.2.2.1 using 1
        simp [QuittingLCPClassification.quittingSingletonMatrix,
          quittingSoloReward]
        ring
    rw [afterTwoValue]
    convert hresult using 1
    · ring
    · congr 2
  · change targetValue reward mass 3 = _
    dsimp [targetValue]
    apply weighted_quotient_eq w.normalizedWeightZero w.normalizedWeightOne
      w.normalizedWeightTwo w.normalizedWeightThree (1 - A)
      (quittingSoloReward reward 0 3) (quittingSoloReward reward 1 3)
      (quittingSoloReward reward 2 3) (quittingSoloReward reward 3 3)
      (quittingSoloReward reward 3 3)
    · exact one_sub_period_ne mass
    · simpa [w, A] using hsum
    · have hA : A ≠ 0 := ne_of_gt mass.periodSurvival_pos
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
    coarseValue reward mass phase phase = quittingSoloReward reward phase phase := by
  rw [coarse_bellman reward mass phase]
  change phaseHazard mass phase * quittingSoloReward reward phase phase +
      (1 - phaseHazard mass phase) *
        coarseValue reward mass (finRotate 4 phase) phase = _
  rw [next_coarse_owner_eq mass hbalances phase]
  ring

omit hbalances in
theorem phaseHazard_pos_and_lt_one (phase : Fin 4) :
    0 < phaseHazard mass phase ∧ phaseHazard mass phase < 1 := by
  have h := mass.hazard_pos_and_lt_one
  fin_cases phase
  · simpa [phaseHazard] using h.1
  · simpa [phaseHazard] using h.2.1
  · simpa [phaseHazard] using h.2.2.1
  · simpa [phaseHazard] using h.2.2.2

include data

theorem coarse_two_after_owner_gt (owner : Fin 4) :
    quittingSoloReward reward owner owner <
      coarseValue reward mass (owner + 2) owner := by
  have hhazard := phaseHazard_pos_and_lt_one mass (owner + 1)
  have harc := congrFun (coarse_bellman reward mass (owner + 1)) owner
  have hprevious := next_coarse_owner_eq mass hbalances owner
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
      coarseValue reward mass (owner + 3) owner := by
  have hhazard := phaseHazard_pos_and_lt_one mass (owner + 3)
  have harc := congrFun (coarse_bellman reward mass (owner + 3)) owner
  have hactive := coarse_active mass hbalances owner
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
    quittingSoloReward reward who who ≤ coarseValue reward mass phase who := by
  fin_cases who <;> fin_cases phase
  all_goals first
    | exact (coarse_active mass hbalances _).ge
    | exact (next_coarse_owner_eq mass hbalances _).ge
    | exact (coarse_two_after_owner_gt data mass hbalances _).le
    | exact (coarse_three_after_owner_gt data mass hbalances _).le

def certificate : BalancedSingletonCycleCertificate (L := 4) reward where
  owner := id
  hazard := phaseHazard mass
  coarse := coarseValue reward mass
  initial := 0
  hazard_nonneg := fun phase => (phaseHazard_pos_and_lt_one mass phase).1.le
  hazard_lt_one := fun phase => (phaseHazard_pos_and_lt_one mass phase).2
  arc := coarse_bellman reward mass
  active := coarse_active mass hbalances
  soloFloor := coarse_soloFloor data mass hbalances
  opponentDivergence := by
    intro who
    refine ⟨who + 1, ?_, (phaseHazard_pos_and_lt_one mass (who + 1)).1⟩
    fin_cases who <;> decide

/-- Under the displayed mass and balance hypotheses, the resolvent target is
a fixed uniform-equilibrium payoff against unrestricted behavioral deviations. -/
theorem targetValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none (targetValue reward mass) := by
  simpa [certificate, coarseValue] using
    (certificate data mass hbalances).isUniformEquilibriumPayoff

end FourPhaseSingletonValues
end GameTheory
