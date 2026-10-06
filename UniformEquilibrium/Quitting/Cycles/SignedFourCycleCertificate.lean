import UniformEquilibrium.Quitting.Cycles.FourPhaseSingletonCertificate
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleValues

noncomputable section

namespace GameTheory
namespace SignedFourCycleSingletonData

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable (data : SignedFourCycleSingletonData reward) (tests : data.StrictTests)

theorem next_coarse_owner_eq (phase : Fin 4) :
    data.coarseValue tests (finRotate 4 phase) phase =
      quittingSoloReward reward phase phase := by
  exact FourPhaseSingletonValues.next_coarse_owner_eq tests.weights.positiveMass
    (data.weighted_singleton_comparison_balances tests) phase

theorem coarse_active (phase : Fin 4) :
    data.coarseValue tests phase phase = quittingSoloReward reward phase phase := by
  exact FourPhaseSingletonValues.coarse_active tests.weights.positiveMass
    (data.weighted_singleton_comparison_balances tests) phase

theorem phaseHazard_pos_and_lt_one (phase : Fin 4) :
    0 < data.phaseHazard tests phase ∧ data.phaseHazard tests phase < 1 := by
  exact FourPhaseSingletonValues.phaseHazard_pos_and_lt_one tests.weights.positiveMass phase

theorem coarse_two_after_owner_gt (owner : Fin 4) :
    quittingSoloReward reward owner owner <
      data.coarseValue tests (owner + 2) owner := by
  exact FourPhaseSingletonValues.coarse_two_after_owner_gt data tests.weights.positiveMass
    (data.weighted_singleton_comparison_balances tests) owner

theorem coarse_three_after_owner_gt (owner : Fin 4) :
    quittingSoloReward reward owner owner <
      data.coarseValue tests (owner + 3) owner := by
  exact FourPhaseSingletonValues.coarse_three_after_owner_gt data tests.weights.positiveMass
    (data.weighted_singleton_comparison_balances tests) owner

theorem coarse_soloFloor (phase who : Fin 4) :
    quittingSoloReward reward who who ≤ data.coarseValue tests phase who := by
  exact FourPhaseSingletonValues.coarse_soloFloor data tests.weights.positiveMass
    (data.weighted_singleton_comparison_balances tests) phase who

def certificate : BalancedSingletonCycleCertificate (L := 4) reward :=
  FourPhaseSingletonValues.certificate data tests.weights.positiveMass
    (data.weighted_singleton_comparison_balances tests)

/-- The geometric-resolvent target constructed from the raw signed table is
a fixed uniform-equilibrium payoff against unrestricted behavioral deviations. -/
theorem targetValue_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none (data.targetValue tests) := by
  exact FourPhaseSingletonValues.targetValue_isUniformEquilibriumPayoff data
    tests.weights.positiveMass (data.weighted_singleton_comparison_balances tests)

end SignedFourCycleSingletonData
end GameTheory
